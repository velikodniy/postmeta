/// <reference lib="deno.ns" />

import { ensureDir } from "@std/fs";
import { dirname, fromFileUrl, join, resolve } from "@std/path";
import type { BuildOptions } from "esbuild";

import { generatedWasmDir } from "./build_wasm.ts";

const scriptDir = dirname(fromFileUrl(import.meta.url));

export const webDir = resolve(scriptDir, "..");
export const distDir = join(webDir, "dist");
export const assetsDir = join(distDir, "assets");

const indexFile = join(webDir, "index.html");
const distIndexFile = join(distDir, "index.html");
const distGeneratedWasmDir = join(distDir, "generated", "postmeta-wasm");

async function copyDirectory(source: string, destination: string): Promise<void> {
  await ensureDir(destination);

  for await (const entry of Deno.readDir(source)) {
    const sourcePath = join(source, entry.name);
    const destinationPath = join(destination, entry.name);

    if (entry.isDirectory) {
      await copyDirectory(sourcePath, destinationPath);
    } else if (entry.isFile) {
      await Deno.copyFile(sourcePath, destinationPath);
    }
  }
}

export async function syncStaticAssets(): Promise<void> {
  await ensureDir(distDir);
  await ensureDir(assetsDir);
  await Deno.copyFile(indexFile, distIndexFile);
  await Deno.remove(distGeneratedWasmDir, { recursive: true }).catch((error: unknown) => {
    if (!(error instanceof Deno.errors.NotFound)) {
      throw error;
    }
  });
  await copyDirectory(generatedWasmDir, distGeneratedWasmDir);
}

export const esbuildBase: BuildOptions = {
  absWorkingDir: webDir,
  entryPoints: {
    app: join(webDir, "src", "main.tsx"),
  },
  outdir: assetsDir,
  entryNames: "[name]",
  assetNames: "[name]",
  bundle: true,
  format: "esm",
  target: ["es2022"],
  jsx: "automatic",
  jsxImportSource: "react",
  loader: {
    ".css": "css",
  },
  legalComments: "none",
  logLevel: "info",
};
