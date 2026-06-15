import { M } from "../Math";

export function Header() {
  return (
    <header className="prose-col pt-10 pb-2 md:pt-12">
      <p
        className="sc-label text-[0.8rem] mb-3"
        style={{ color: "var(--ink-faint)" }}
      >
        machine-checked mathematics &middot; lean 4 &middot; june 2026
      </p>
      <h1
        className="text-[2.1rem] md:text-[2.7rem] font-semibold leading-[1.07]"
        style={{ letterSpacing: "-0.02em" }}
      >
        The Million-Dollar Window
      </h1>
      <p
        className="mt-3 text-[1.05rem] leading-[1.45]"
        style={{ color: "var(--ink-secondary)" }}
      >
        What happened when a swarm of AI agents attacked one of
        Ethereum&rsquo;s hardest open math problems, with a proof checker as
        referee.
      </p>
      <p className="mt-3 text-[0.88rem]" style={{ color: "var(--ink-faint)" }}>
        A campaign report on the mutual correlated agreement threshold{" "}
        <M>{String.raw`\delta^*`}</M> for smooth Reed&ndash;Solomon codes
        &middot; the ArkLib <M>{String.raw`\delta^*`}</M> campaign &middot; an
        LLM agent fleet writing Lean&nbsp;4, verified by the Lean kernel
      </p>
      <p className="mt-1.5 text-[0.88rem]" style={{ color: "var(--ink-faint)" }}>
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>
        {" "}&middot;{" "}
        <a href="https://github.com/lalalune/ArkLib/issues/407">
          campaign log: issues #232 &rarr; #334 &rarr; #357 &rarr; #371 &rarr; #389 &rarr; #407
        </a>
      </p>
      <div
        className="mt-5 mb-2 h-px w-full"
        style={{ background: "var(--rule)" }}
      />
    </header>
  );
}
