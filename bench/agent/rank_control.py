#!/usr/bin/env python3
"""rank_control.py — negative control: does the premise selector learn the REAL
premise graph, or just token statistics?

The energy ranker's win (rank_train_eval.py, R@1 ~36x floor) only means something if it
beats a control that shares the data's tokens but destroys its *structure*. So we train
the same model two ways and evaluate on the same held-out TRUE pairs:

  true     : train on real (statement -> used-premise) pairs.
  shuffled : train on (statement -> RANDOM premise) pairs — same tokens, pairing destroyed.

If `true` recall >> `shuffled` recall, the selector is learning the genuine premise
dependency structure, not memorizing token frequencies (anti-Goodhart). This is the
structural-recovery control for the bench/agent corroboration suite.

Self-contained: torch only, deterministic. Run: python3 bench/agent/rank_control.py
"""
from __future__ import annotations
import json, os, random, sys
from collections import Counter
from pathlib import Path
import torch

from ebm_core import MiniTransformer, tokenize, SPECIAL_TOKENS, infonce_energy_loss, run_probe, MAX_LEN

HERE = Path(__file__).resolve().parent
DATA = HERE / "arklib_premises.jsonl"
DEVICE = torch.device("mps" if torch.backends.mps.is_available() else "cpu")
SEED = 7


def build_vocab(pairs, top_k=8000):
    c = Counter()
    for p in pairs:
        c.update(tokenize(p["a"])); c.update(tokenize(p["b"]))
    v = {t: i for i, t in enumerate(SPECIAL_TOKENS)}
    for w, _ in c.most_common(top_k - len(SPECIAL_TOKENS)):
        v[w] = len(v)
    return v


def train(pairs, vocab, epochs):
    torch.manual_seed(SEED)
    model = MiniTransformer(len(vocab), max_len=MAX_LEN).to(DEVICE)
    opt = torch.optim.AdamW(model.parameters(), lr=3e-4, weight_decay=0.01)
    model.train()
    for ep in range(epochs):
        random.Random(SEED + ep).shuffle(pairs)
        for i in range(0, len(pairs), 64):
            batch = pairs[i:i + 64]
            if len(batch) < 2:
                continue
            loss = infonce_energy_loss(model, {"items": batch}, vocab, DEVICE)
            opt.zero_grad(); loss.backward(); opt.step()
    model.eval()
    return model


def main():
    if not DATA.exists():
        sys.exit("no mined pairs — run: python3 bench/agent/mine_premises.py")
    pairs = [json.loads(l) for l in DATA.read_text().splitlines() if l.strip()]
    for i, p in enumerate(pairs):
        p["ref"] = f"r{i}"
    rng = random.Random(SEED); rng.shuffle(pairs)
    vocab = build_vocab(pairs)
    n_eval_full = max(60, int(len(pairs) * 0.15))
    eval_full, train_full = pairs[:n_eval_full], pairs[n_eval_full:]
    # Fast config: the true-vs-shuffled gap is large, so a subsample gives the same verdict
    # far quicker (the probe is latency-bound). Override via env for a fuller run.
    K = int(os.environ.get("ARKLIB_EBM_K", "20"))
    train_ = train_full[: int(os.environ.get("ARKLIB_EBM_NTRAIN", "4000"))]
    eval_ = eval_full[: int(os.environ.get("ARKLIB_EBM_NEVAL", "80"))]
    epochs = int(os.environ.get("ARKLIB_EBM_EPOCHS", "5"))

    # true arm
    m_true = train([dict(x) for x in train_], vocab, epochs)
    r_true = run_probe(m_true, eval_, pairs, vocab, DEVICE, k=K, seed=0)

    # shuffled control: same statements, permuted premises (pairing destroyed)
    bs = [x["b"] for x in train_]
    perm = list(range(len(bs))); random.Random(123).shuffle(perm)
    train_shuf = [{"a": train_[i]["a"], "b": bs[perm[i]], "ref": train_[i]["ref"]} for i in range(len(train_))]
    m_shuf = train(train_shuf, vocab, epochs)
    r_shuf = run_probe(m_shuf, eval_, pairs, vocab, DEVICE, k=K, seed=0)

    floor = round(1 / K, 4)
    print(f"=== premise selector — structural-recovery control "
          f"(train={len(train_)}, held-out n={len(eval_)}, k={K}) ===")
    print(f"  trained on TRUE pairs     : R@1={r_true['R@1']}  MRR={r_true['MRR']}")
    print(f"  trained on SHUFFLED pairs : R@1={r_shuf['R@1']}  MRR={r_shuf['MRR']}")
    print(f"  random floor              : {floor}")
    print(f"  true / shuffled           : {r_true['R@1']/max(1e-9,r_shuf['R@1']):.1f}x")
    out = {"true_R@1": r_true["R@1"], "shuffled_R@1": r_shuf["R@1"], "floor": floor}
    (HERE / "rank_control_result.json").write_text(json.dumps(out, indent=2))
    # witness: the selector learns real structure iff true decisively beats the shuffled control.
    ok = r_true["R@1"] >= 3 * max(r_shuf["R@1"], floor)
    print(f"  -> {'PASS' if ok else 'FAIL'} (true beats structure-destroyed control)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
