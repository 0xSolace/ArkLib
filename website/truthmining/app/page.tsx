import { MiningRig } from "@/components/MiningRig";
import { M } from "@/components/Math";

const DELTASTAR = "https://deltastar.computer";
const CONTACT = "https://github.com/lalalune/ArkLib";

export default function Page() {
  return (
    <main className="relative">
      {/* ============================ NAV ============================ */}
      <header className="col flex items-center justify-between pt-7 pb-2 relative z-10">
        <div className="flex items-center gap-2.5">
          <span
            className="inline-block rounded-[3px]"
            style={{
              width: "0.85rem",
              height: "0.85rem",
              background: "var(--ok)",
              boxShadow: "0 0 16px -2px var(--ok-glow)",
            }}
          />
          <span className="mono text-[0.82rem]" style={{ letterSpacing: "0.02em" }}>
            truth&#8202;mining
          </span>
        </div>
        <nav className="hidden sm:flex items-center gap-7 mono text-[0.74rem]" style={{ color: "var(--ink-2)" }}>
          <a className="link" href="#manifesto" style={{ textDecorationColor: "transparent" }}>
            manifesto
          </a>
          <a className="link" href="#proof" style={{ textDecorationColor: "transparent" }}>
            the proof
          </a>
          <a className="link" href="#frontier" style={{ textDecorationColor: "transparent" }}>
            the frontier
          </a>
        </nav>
      </header>

      {/* ============================ HERO ============================ */}
      <section
        className="relative col"
        style={{ paddingTop: "clamp(5rem, 13vw, 11rem)", paddingBottom: "clamp(4rem, 10vw, 8rem)" }}
      >
        <div className="field-grid" style={{ height: "130%" }} />
        <div className="relative">
          <p className="eyebrow rise d1 mb-8">proof of work, except the work is real</p>
          <h1
            className="display rise d2"
            style={{ fontSize: "clamp(3.6rem, 16vw, 13rem)", lineHeight: 0.9 }}
          >
            We mine
            <br />
            <span style={{ color: "var(--ok)" }}>truth.</span>
          </h1>
          <div className="rise d3 mt-12 lg:mt-16">
            <MiningRig />
          </div>
          <p className="rise d4 mono text-[0.72rem] mt-8" style={{ color: "var(--ink-3)" }}>
            compute resolves a candidate · a kernel checks it · a false truth does not typecheck
          </p>
        </div>
      </section>

      {/* ========================= THE MANIFESTO ========================= */}
      <section id="manifesto" className="relative">
        <Beat
          index="01"
          line={
            <>
              Bitcoin spends compute to mine hashes
              <br className="hidden sm:block" /> that{" "}
              <span style={{ color: "var(--ink-3)" }}>prove nothing.</span>
            </>
          }
        />
        <Beat
          index="02"
          line={
            <>
              We spend compute to mine things
              <br className="hidden sm:block" /> that are{" "}
              <span style={{ color: "var(--ok)" }}>true.</span>
            </>
          }
        />
        <Beat
          index="03"
          line={
            <>
              The verifier is a{" "}
              <span style={{ color: "var(--ok)" }}>kernel</span>, not a vote.
              <br className="hidden sm:block" /> It cannot be fooled.
            </>
          }
          sub="Expensive to produce. Trivial to check. Impossible to fake. No partial credit, no consensus to bribe, no oracle to capture."
        />
        <Beat
          index="04"
          line={
            <>
              Compute mines it. A false truth
              <br className="hidden sm:block" /> does not{" "}
              <span style={{ color: "var(--ok)" }}>typecheck.</span>
            </>
          }
          sub="This is a new primitive. Proof of work where the work is real knowledge, manufactured and certified at scale."
        />
      </section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE PROOF IT IS REAL ========================= */}
      <section id="proof" className="col" style={{ paddingBlock: "clamp(5rem, 11vw, 8rem)" }}>
        <p className="eyebrow mb-7">the proof it is real · this happened</p>
        <div className="grid lg:grid-cols-[1.1fr_0.9fr] gap-10 lg:gap-16 items-start">
          <div>
            <h2 style={{ fontSize: "clamp(2rem, 5vw, 3.4rem)", lineHeight: 1.02 }}>
              In one night, a fleet mined a{" "}
              <span style={{ color: "var(--ok)" }}>25-year-open</span> problem.
            </h2>
            <p className="mt-7 measure text-[1.08rem]" style={{ color: "var(--ink-2)" }}>
              The target was <M>{"\\delta^*"}</M>, the open question behind a{" "}
              <span style={{ color: "var(--ink)" }}>$1M</span> Ethereum
              Foundation prize. Around 150 Lean bricks came back: kernel-checked
              theorems, honest refutations, and an audit-guard that caught its
              own false positives. When the kernel rejected a claim, the fleet
              reversed it. Every accepted result typechecked.
            </p>
            <a
              className="link mono text-[0.84rem] inline-flex items-center gap-2 mt-8"
              href={DELTASTAR}
            >
              the first mined truth → deltastar.computer
            </a>
          </div>

          <div className="grid gap-4">
            <div className="brick brick-ok p-7">
              <span className="chip chip-ok mb-4">
                <span className="dot" /> certified
              </span>
              <p className="text-[1.04rem]" style={{ color: "var(--ink)" }}>
                Every accepted result passed the Lean kernel. Not probably
                right. Checkable by anyone, in one command.
              </p>
            </div>
            <div className="brick p-7">
              <span className="chip chip-no mb-4">
                <span className="dot" /> honest
              </span>
              <p className="text-[1.0rem]" style={{ color: "var(--ink-2)" }}>
                The deep wall stays open. <M>{"\\delta^*"}</M> was localized,
                not the whole prize. The guard refused to let the fleet lie
                about it. That refusal is the point.
              </p>
            </div>
          </div>
        </div>
      </section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE FRONTIER ========================= */}
      <section id="frontier" className="col" style={{ paddingBlock: "clamp(5rem, 11vw, 8rem)" }}>
        <p className="eyebrow mb-7">the frontier</p>
        <h2 className="measure" style={{ fontSize: "clamp(2rem, 5.5vw, 3.6rem)", lineHeight: 1.02, maxWidth: "20ch" }}>
          Anywhere a cheap trustless verifier exists,{" "}
          <span style={{ color: "var(--ok)" }}>truth is mineable.</span>
        </h2>
        <p className="mt-7 measure text-[1.08rem]" style={{ color: "var(--ink-2)" }}>
          Mathematics is the beachhead, where the verifier is perfect. From
          there the frontier expands: cryptographic code, then everywhere a
          verifier can be made cheap and trustless. Not everything is mineable
          yet. That boundary is real, and it is the line we push.
        </p>

        <div className="mt-12 grid sm:grid-cols-3 gap-px" style={{ background: "var(--rule)" }}>
          <FrontierCell
            label="mathematics"
            state="ok"
            note="perfect verifier · proven"
          />
          <FrontierCell
            label="cryptographic code"
            state="ok"
            note="cheap trustless verifier · next"
          />
          <FrontierCell
            label="the open frontier"
            state="edge"
            note="wherever a verifier can be built"
          />
        </div>
      </section>

      {/* ============================ QUIET CTA ============================ */}
      <section
        id="contact"
        className="relative"
        style={{ paddingBlock: "clamp(5rem, 12vw, 9rem)" }}
      >
        <div className="field-grid" style={{ top: "auto", bottom: 0, height: "130%", transform: "scaleY(-1)" }} />
        <div className="col relative">
          <h2
            className="display"
            style={{ fontSize: "clamp(2.4rem, 8vw, 6rem)", lineHeight: 0.94, maxWidth: "16ch" }}
          >
            Bring a target.
            <br />
            <span style={{ color: "var(--ok)" }}>We mine it.</span>
          </h2>
          <p className="mono text-[0.86rem] mt-8" style={{ color: "var(--ink-2)" }}>
            build · commission · get in touch ·{" "}
            <a className="link" href={CONTACT}>
              github.com/lalalune/ArkLib
            </a>
          </p>
        </div>
      </section>

      {/* ============================ FOOTER ============================ */}
      <footer className="col" style={{ paddingBottom: "clamp(3rem, 6vw, 5rem)" }}>
        <hr className="rule mb-7" />
        <div className="flex flex-col sm:flex-row items-start sm:items-center justify-between gap-4">
          <div className="flex items-center gap-2.5">
            <span
              className="inline-block rounded-[3px]"
              style={{ width: "0.7rem", height: "0.7rem", background: "var(--ok)" }}
            />
            <span className="mono text-[0.78rem]">truth&#8202;mining</span>
          </div>
          <p className="mono text-[0.72rem]" style={{ color: "var(--ink-3)" }}>
            the unit of work is a brick · one kernel-checked theorem or refutation
          </p>
          <a className="link mono text-[0.74rem]" href={DELTASTAR}>
            deltastar.computer
          </a>
        </div>
      </footer>
    </main>
  );
}

/* ----------------------------- manifesto beat ---------------------------- */
function Beat({
  index,
  line,
  sub,
}: {
  index: string;
  line: React.ReactNode;
  sub?: string;
}) {
  return (
    <div className="col" style={{ paddingBlock: "clamp(4rem, 10vw, 8rem)" }}>
      <div className="flex items-start gap-5 sm:gap-8">
        <span
          className="mono pt-3 shrink-0"
          style={{ color: "var(--ink-faint)", fontSize: "0.78rem", letterSpacing: "0.1em" }}
        >
          {index}
        </span>
        <div>
          <p
            className="display"
            style={{ fontSize: "clamp(2.1rem, 6.5vw, 5rem)", lineHeight: 1.0 }}
          >
            {line}
          </p>
          {sub ? (
            <p className="mt-7 measure text-[1.08rem]" style={{ color: "var(--ink-2)" }}>
              {sub}
            </p>
          ) : null}
        </div>
      </div>
    </div>
  );
}

/* ----------------------------- frontier cell ----------------------------- */
function FrontierCell({
  label,
  state,
  note,
}: {
  label: string;
  state: "ok" | "edge";
  note: string;
}) {
  const color = state === "ok" ? "var(--ok)" : "var(--no)";
  return (
    <div className="p-7" style={{ background: "var(--bg)" }}>
      <span className="flex items-center gap-2.5 mono text-[0.7rem]" style={{ color }}>
        <span
          className="inline-block"
          style={{
            width: "0.5rem",
            height: "0.5rem",
            borderRadius: state === "ok" ? "2px" : "999px",
            background: color,
            boxShadow: state === "ok" ? "0 0 12px -2px var(--ok-glow)" : "none",
          }}
        />
        {state === "ok" ? "mineable" : "frontier"}
      </span>
      <p className="mt-5 text-[1.16rem]" style={{ color: "var(--ink)" }}>
        {label}
      </p>
      <p className="mono text-[0.72rem] mt-2" style={{ color: "var(--ink-3)" }}>
        {note}
      </p>
    </div>
  );
}
