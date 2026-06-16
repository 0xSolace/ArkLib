"use client";

import { useState } from "react";

/**
 * A shell command rendered as a click-to-copy block. Keeps the site static
 * (no runtime deps) — the only client interactivity on the page besides the
 * degen toggle. The displayed text and the copied text are the same string.
 */
export function CopyCommand({ command }: { command: string }) {
  const [copied, setCopied] = useState(false);

  function flash() {
    setCopied(true);
    window.setTimeout(() => setCopied(false), 1500);
  }

  function fallback() {
    try {
      const ta = document.createElement("textarea");
      ta.value = command;
      ta.style.position = "fixed";
      ta.style.top = "-9999px";
      ta.setAttribute("readonly", "");
      document.body.appendChild(ta);
      ta.select();
      document.execCommand("copy");
      document.body.removeChild(ta);
      flash();
    } catch {
      /* clipboard unavailable — the command stays selectable for manual copy */
    }
  }

  function copy() {
    if (navigator.clipboard?.writeText) {
      navigator.clipboard.writeText(command).then(flash, fallback);
    } else {
      fallback();
    }
  }

  return (
    <button
      type="button"
      className="cmd"
      onClick={copy}
      aria-label={`Copy command: ${command}`}
    >
      <code>{command}</code>
      <span className="cmd-copy" aria-hidden>
        {copied ? "copied ✓" : "copy"}
      </span>
    </button>
  );
}
