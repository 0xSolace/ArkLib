"use client";

import { useEffect, useRef, type ReactNode } from "react";
import { annotate } from "rough-notation";
import { useDegen } from "./degen/DegenProvider";

type ScribbleType =
  | "underline"
  | "circle"
  | "box"
  | "highlight"
  | "strike-through"
  | "crossed-off"
  | "bracket";

/** Map semantic tones onto the paper's CSS custom properties. */
const TONE_VAR: Record<string, string> = {
  accent: "--accent",
  ink: "--ink-secondary",
  verified: "--verified",
  refuted: "--refuted",
  soft: "--accent-soft",
};

/**
 * Hand-drawn marginalia via rough-notation. rough-notation draws its SVG at the
 * element's position *at draw time* and does not follow later layout shifts — so
 * the annotation is recreated whenever the layout can move under it: on the degen
 * toggle (which inserts/removes ELI5 panels) and on window resize. First reveal
 * animates on scroll-into-view; subsequent redraws are instant and in place.
 */
export function Scribble({
  type = "underline",
  tone = "accent",
  strokeWidth,
  padding,
  multiline = true,
  delay = 0,
  children,
}: {
  type?: ScribbleType;
  tone?: keyof typeof TONE_VAR;
  strokeWidth?: number;
  padding?: number;
  multiline?: boolean;
  delay?: number;
  children: ReactNode;
}) {
  const ref = useRef<HTMLSpanElement>(null);
  const shownRef = useRef(false);
  const { degen } = useDegen();

  useEffect(() => {
    const el = ref.current;
    if (!el) return;
    if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) return;

    const cssVar = TONE_VAR[tone] ?? "--accent";
    const color =
      getComputedStyle(document.documentElement)
        .getPropertyValue(cssVar)
        .trim() || "#8a3033";

    const make = (animate: boolean) =>
      annotate(el, {
        type,
        color,
        strokeWidth: strokeWidth ?? (type === "highlight" ? 1 : 1.5),
        padding: padding ?? (type === "circle" ? 6 : type === "box" ? 4 : 2),
        multiline,
        iterations: 2,
        animationDuration: animate ? 800 : 0,
      });

    let annotation = make(true);
    let timer: ReturnType<typeof setTimeout> | undefined;
    let resizeTimer: ReturnType<typeof setTimeout> | undefined;
    let io: IntersectionObserver | undefined;

    if (shownRef.current) {
      // already revealed once (e.g. the degen toggle re-ran this effect) —
      // redraw instantly at the new position, no scroll wait, no animation.
      annotation.remove();
      annotation = make(false);
      annotation.show();
    } else {
      io = new IntersectionObserver(
        (entries) => {
          for (const entry of entries) {
            if (entry.isIntersecting) {
              timer = setTimeout(() => {
                annotation.show();
                shownRef.current = true;
              }, delay);
              io?.disconnect();
            }
          }
        },
        { threshold: 0.5, rootMargin: "0px 0px -8% 0px" },
      );
      io.observe(el);
    }

    const onResize = () => {
      if (!shownRef.current) return;
      if (resizeTimer) clearTimeout(resizeTimer);
      resizeTimer = setTimeout(() => {
        annotation.remove();
        annotation = make(false);
        annotation.show();
      }, 120);
    };
    window.addEventListener("resize", onResize);

    return () => {
      io?.disconnect();
      if (timer) clearTimeout(timer);
      if (resizeTimer) clearTimeout(resizeTimer);
      window.removeEventListener("resize", onResize);
      annotation.remove();
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [degen]);

  return <span ref={ref}>{children}</span>;
}
