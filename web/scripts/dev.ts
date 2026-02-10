/// <reference lib="deno.ns" />

import { emptyDir } from "@std/fs";
import * as esbuild from "esbuild";

import { buildWasm, generatedWasmDir } from "./build_wasm.ts";
import { assetsDir, distDir, esbuildBase, syncStaticAssets, webDir } from "./common.ts";

const indexFile = new URL("../index.html", import.meta.url).pathname;

async function startDev(): Promise<void> {
  await buildWasm();
  await emptyDir(distDir);
  await syncStaticAssets();

  const context = await esbuild.context({
    ...esbuildBase,
    minify: false,
    sourcemap: true,
  });

  await context.watch();
  const server = await context.serve({
    servedir: distDir,
    port: 5173,
  });

  const host = server.hosts[0] ?? "localhost";

  console.log(`Dev server running on http://${host}:${server.port}`);
  console.log("Re-run `deno task wasm` if Rust sources change.");

  const watcher = Deno.watchFs([indexFile, generatedWasmDir], { recursive: true });
  for await (const _event of watcher) {
    await syncStaticAssets();
  }
}

if (import.meta.main) {
  await startDev();
}
