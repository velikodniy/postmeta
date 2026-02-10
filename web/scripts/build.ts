/// <reference lib="deno.ns" />

import { emptyDir } from "@std/fs";
import * as esbuild from "esbuild";

import { buildWasm } from "./build_wasm.ts";
import { distDir, esbuildBase, syncStaticAssets } from "./common.ts";

export async function buildSite(): Promise<void> {
  await buildWasm();
  await emptyDir(distDir);
  await syncStaticAssets();

  try {
    await esbuild.build({
      ...esbuildBase,
      minify: true,
      sourcemap: false,
    });
  } finally {
    esbuild.stop();
  }

  console.log(`Static site ready: ${distDir}`);
}

if (import.meta.main) {
  await buildSite();
}
