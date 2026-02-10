import { HighlightStyle, StreamLanguage, syntaxHighlighting } from "@codemirror/language";
import type { Extension } from "@codemirror/state";
import { EditorView } from "@codemirror/view";
import { tags as t } from "@lezer/highlight";

const keywords = new Set([
  "beginfig",
  "endfig",
  "draw",
  "fill",
  "filldraw",
  "undraw",
  "unfill",
  "pickup",
  "for",
  "forsuffixes",
  "forever",
  "endfor",
  "step",
  "until",
  "if",
  "elseif",
  "else",
  "fi",
  "save",
  "interim",
  "let",
  "input",
  "show",
  "shipout",
  "clip",
  "setbounds",
  "withpen",
  "withcolor",
  "dashed",
  "scaled",
  "shifted",
  "rotated",
  "xscaled",
  "yscaled",
  "zscaled",
  "slanted",
  "transformed",
  "def",
  "vardef",
  "primarydef",
  "secondarydef",
  "tertiarydef",
  "enddef",
  "numeric",
  "pair",
  "path",
  "pen",
  "picture",
  "color",
  "transform",
  "string",
  "boolean",
]);

const atoms = new Set([
  "true",
  "false",
  "cycle",
  "nullpicture",
  "nullpen",
  "origin",
  "up",
  "down",
  "left",
  "right",
  "fullcircle",
  "unitsquare",
]);

interface ParserState {
  inString: boolean;
}

const parser = {
  startState(): ParserState {
    return { inString: false };
  },

  token(stream: any, state: ParserState): string | null {
    if (state.inString) {
      while (!stream.eol()) {
        if (stream.next() === '"') {
          state.inString = false;
          break;
        }
      }
      return "string";
    }

    if (stream.eatSpace()) {
      return null;
    }

    if (stream.peek() === "%") {
      stream.skipToEnd();
      return "comment";
    }

    if (stream.peek() === '"') {
      stream.next();
      state.inString = true;
      return "string";
    }

    if (stream.match(/^(\.{3}|---|--|\.\.|\+\+|\+-\+|:=|<=|>=|<>)/)) {
      return "operator";
    }

    if (stream.match(/^[+\-*/=<>&]/)) {
      return "operator";
    }

    if (stream.match(/^[\[\]{}(),;:]/)) {
      return "bracket";
    }

    if (stream.match(/^\d*\.?\d+(e[-+]?\d+)?/i)) {
      return "number";
    }

    if (stream.match(/^[A-Za-z_][A-Za-z0-9_]*/)) {
      const word = stream.current();
      if (keywords.has(word)) {
        return "keyword";
      }
      if (atoms.has(word)) {
        return "atom";
      }
      return "variableName";
    }

    stream.next();
    return null;
  },
};

const metapostHighlight = HighlightStyle.define([
  { tag: t.keyword, color: "#17606a", fontWeight: "600" },
  { tag: t.atom, color: "#87465f" },
  { tag: t.comment, color: "#7b8277", fontStyle: "italic" },
  { tag: t.string, color: "#99511d" },
  { tag: t.number, color: "#224f9f" },
  { tag: t.operator, color: "#5b546b" },
  { tag: t.variableName, color: "#243328" },
  { tag: t.bracket, color: "#5b546b" },
]);

const editorTheme = EditorView.theme({
  "&": {
    height: "100%",
    color: "#1f2521",
    backgroundColor: "#fffef9",
    fontFamily: '"JetBrains Mono", "SF Mono", Menlo, Consolas, monospace',
    fontSize: "14px",
  },
  ".cm-content": {
    caretColor: "#136978",
    padding: "16px 0",
  },
  ".cm-line": {
    padding: "0 14px",
  },
  ".cm-gutters": {
    backgroundColor: "#f6f2e7",
    color: "#8a8f82",
    borderRight: "1px solid #ddd8cc",
  },
  ".cm-activeLine": {
    backgroundColor: "rgba(19, 105, 120, 0.06)",
  },
  ".cm-activeLineGutter": {
    backgroundColor: "rgba(19, 105, 120, 0.08)",
  },
  ".cm-selectionBackground, &.cm-focused .cm-selectionBackground": {
    backgroundColor: "rgba(16, 112, 128, 0.20)",
  },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "#136978",
  },
});

export const metapostExtensions: Extension[] = [
  StreamLanguage.define(parser),
  syntaxHighlighting(metapostHighlight),
  editorTheme,
];
