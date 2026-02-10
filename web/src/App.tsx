import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import type { PointerEvent as ReactPointerEvent, WheelEvent as ReactWheelEvent } from "react";
import CodeMirror from "@uiw/react-codemirror";
import { EditorState } from "@codemirror/state";

import { metapostExtensions } from "./editor/metapostLanguage.ts";
import { compilePostMeta } from "./engine/postmeta.ts";

const RENDER_DELAY_MS = 550;
const MIN_SCALE = 0.5;
const MAX_SCALE = 5;
const ZOOM_STEP = 1.12;

const defaultProgram = `beginfig(1);
  numeric R, ring, petals;
  R := 150;
  ring := 110;
  petals := 36;

  fill fullcircle scaled (2*R) withcolor (0.98, 0.96, 0.91);

  for i = 0 step 1 until petals-1:
    pair p, q;
    p := dir(360*i/petals) scaled ring;
    q := dir(360*(i+9)/petals) scaled ring;
    draw p..origin..q
      withpen pencircle scaled 0.7
      withcolor (
        0.35 + 0.30*sind(7*i),
        0.45 + 0.25*cosd(5*i),
        0.50 + 0.30*sind(9*i)
      );
  endfor;

  for a = 0 step 12 until 348:
    fill fullcircle scaled 14 shifted (dir(a) scaled ring)
      withcolor (0.93, 0.36, 0.24);
  endfor;

  for a = 0 step 30 until 330:
    draw (0,0)--(dir(a) scaled R)
      withpen pencircle scaled 1.2
      withcolor (0.13, 0.18, 0.26);
  endfor;

  draw fullcircle scaled (2*R)
    withpen pencircle scaled 1.4
    withcolor (0.13, 0.18, 0.26);

  draw fullcircle scaled (2*ring)
    withpen pencircle scaled 0.9
    withcolor (0.25, 0.29, 0.38);

  fill fullcircle scaled 24 withcolor (0.11, 0.15, 0.23);
  fill fullcircle scaled 8 withcolor (0.97, 0.72, 0.19);
endfig;`;

export function App() {
  const [source, setSource] = useState(defaultProgram);
  const [svg, setSvg] = useState("");
  const [diagnostics, setDiagnostics] = useState("");
  const [hasError, setHasError] = useState(false);
  const [scale, setScale] = useState(1);
  const [offset, setOffset] = useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = useState(false);

  const renderTokenRef = useRef(0);
  const dragRef = useRef<{ pointerId: number; x: number; y: number } | null>(null);

  const editorExtensions = useMemo(
    () => [
      ...metapostExtensions,
      EditorState.tabSize.of(2),
    ],
    [],
  );

  const svgDataUrl = useMemo(() => {
    if (svg.length === 0) {
      return "";
    }
    return `data:image/svg+xml;charset=utf-8,${encodeURIComponent(svg)}`;
  }, [svg]);

  useEffect(() => {
    setScale(1);
    setOffset({ x: 0, y: 0 });
    setIsDragging(false);
    dragRef.current = null;
  }, [svgDataUrl]);

  const clampScale = useCallback((value: number): number => {
    return Math.min(MAX_SCALE, Math.max(MIN_SCALE, value));
  }, []);

  const handleDownloadSvg = useCallback(() => {
    if (svg.length === 0) {
      return;
    }

    const blob = new Blob([svg], { type: "image/svg+xml;charset=utf-8" });
    const url = URL.createObjectURL(blob);

    const anchor = document.createElement("a");
    anchor.href = url;
    anchor.download = "metapost-output.svg";
    anchor.click();

    setTimeout(() => {
      URL.revokeObjectURL(url);
    }, 0);
  }, [svg]);

  const handleCanvasWheel = useCallback((event: ReactWheelEvent<HTMLDivElement>) => {
    if (svgDataUrl.length === 0) {
      return;
    }

    event.preventDefault();
    setScale((current: number) => {
      const factor = event.deltaY < 0 ? ZOOM_STEP : 1 / ZOOM_STEP;
      return clampScale(current * factor);
    });
  }, [clampScale, svgDataUrl.length]);

  const handlePointerDown = useCallback((event: ReactPointerEvent<HTMLDivElement>) => {
    if (svgDataUrl.length === 0 || event.button !== 0) {
      return;
    }

    event.currentTarget.setPointerCapture(event.pointerId);
    dragRef.current = { pointerId: event.pointerId, x: event.clientX, y: event.clientY };
    setIsDragging(true);
  }, [svgDataUrl.length]);

  const handlePointerMove = useCallback((event: ReactPointerEvent<HTMLDivElement>) => {
    const activeDrag = dragRef.current;
    if (!activeDrag || activeDrag.pointerId !== event.pointerId) {
      return;
    }

    const dx = event.clientX - activeDrag.x;
    const dy = event.clientY - activeDrag.y;

    dragRef.current = {
      pointerId: event.pointerId,
      x: event.clientX,
      y: event.clientY,
    };

    setOffset((current: { x: number; y: number }) => ({ x: current.x + dx, y: current.y + dy }));
  }, []);

  const finishDrag = useCallback((event: ReactPointerEvent<HTMLDivElement>) => {
    const activeDrag = dragRef.current;
    if (!activeDrag || activeDrag.pointerId !== event.pointerId) {
      return;
    }

    if (event.currentTarget.hasPointerCapture(event.pointerId)) {
      event.currentTarget.releasePointerCapture(event.pointerId);
    }

    dragRef.current = null;
    setIsDragging(false);
  }, []);

  const handleResetView = useCallback(() => {
    setScale(1);
    setOffset({ x: 0, y: 0 });
  }, []);

  const blockPreviewCanvasPointer = useCallback((event: ReactPointerEvent<HTMLElement>) => {
    event.stopPropagation();
  }, []);

  const renderProgram = useCallback(async (program: string) => {
    const renderToken = ++renderTokenRef.current;

    const result = await compilePostMeta(program);
    if (renderToken !== renderTokenRef.current) {
      return;
    }

    if (result.svg.length > 0 || !result.hasError) {
      setSvg(result.svg);
    }

    if (result.hasError) {
      const diagnosticText = result.diagnostics.length > 0
        ? result.diagnostics
        : "error no diagnostics were returned";
      setDiagnostics(diagnosticText);
    } else {
      setDiagnostics("");
    }

    setHasError(result.hasError);
  }, []);

  useEffect(() => {
    const handle = setTimeout(() => {
      void renderProgram(source);
    }, RENDER_DELAY_MS);

    return () => {
      clearTimeout(handle);
    };
  }, [renderProgram, source]);

  return (
    <main className="app-shell">
      <header className="topbar">
        <div>
          <h1>MetaPost Playground</h1>
          <p className="subtitle">
            Powered by <a href="https://github.com/velikodniy/postmeta" target="_blank" rel="noreferrer">PostMeta</a>
          </p>
        </div>
      </header>

      <section className="workspace">
        <article className="panel editor-panel">
          <div className="editor-shell">
            <CodeMirror
              value={source}
              height="100%"
              extensions={editorExtensions}
              onChange={(value: string) => setSource(value)}
              basicSetup={{
                foldGutter: false,
                allowMultipleSelections: false,
                highlightActiveLine: true,
                highlightActiveLineGutter: true,
                autocompletion: false,
              }}
            />
          </div>
        </article>

        <article className="panel preview-panel">
          <div
            className={`preview-canvas${isDragging ? " dragging" : ""}`}
            aria-live="polite"
            onWheel={handleCanvasWheel}
            onPointerDown={handlePointerDown}
            onPointerMove={handlePointerMove}
            onPointerUp={finishDrag}
            onPointerCancel={finishDrag}
            onDoubleClick={handleResetView}
          >
            {svgDataUrl.length > 0
              ? (
                <div className="svg-scroll">
                  <div
                    className="svg-stage"
                    style={{ transform: `translate(${offset.x}px, ${offset.y}px) scale(${scale})` }}
                  >
                    <img
                      className="svg-image"
                      src={svgDataUrl}
                      alt="MetaPost output"
                      draggable={false}
                    />
                  </div>
                  <div className="image-tools" onPointerDown={blockPreviewCanvasPointer}>
                    <button
                      className="image-tool"
                      type="button"
                      onClick={handleResetView}
                      aria-label="Reset view"
                      title="Reset view"
                    >
                      <svg viewBox="0 0 24 24" role="presentation" aria-hidden="true">
                        <path d="M12 6V3L8 7l4 4V8c2.76 0 5 2.24 5 5 0 1.12-.38 2.2-1.08 3.06l1.46 1.46A6.93 6.93 0 0 0 19 13c0-3.87-3.13-7-7-7Zm-5 5c0-1.12.38-2.2 1.08-3.06L6.62 6.48A6.93 6.93 0 0 0 5 11c0 3.87 3.13 7 7 7v3l4-4-4-4v3c-2.76 0-5-2.24-5-5Z" />
                      </svg>
                    </button>
                    <button
                      className="image-tool"
                      type="button"
                      onClick={handleDownloadSvg}
                      aria-label="Download SVG"
                      title="Download SVG"
                    >
                      <svg viewBox="0 0 24 24" role="presentation" aria-hidden="true">
                        <path d="M5 20h14v-2H5v2Zm7-18v10.17l3.59-3.58L17 10l-5 5-5-5 1.41-1.41L11 12.17V2h1Z" />
                      </svg>
                    </button>
                  </div>
                </div>
              )
              : <div className="preview-empty">No SVG output yet.</div>}
          </div>
          {hasError
            ? (
              <div className="diagnostics-wrap">
                <h3>Diagnostics</h3>
                <pre className="diagnostics error">{diagnostics}</pre>
              </div>
            )
            : null}
        </article>
      </section>
    </main>
  );
}
