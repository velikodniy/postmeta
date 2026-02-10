import { ensureDir } from "@std/fs";
import { dirname, fromFileUrl, join, resolve } from "@std/path";

const decoder = new TextDecoder();

const scriptDir = dirname(fromFileUrl(import.meta.url));
const webDir = resolve(scriptDir, "..");
const crateDir = resolve(webDir, "..", "postmeta-wasm");

export const generatedWasmDir = join(webDir, "generated", "postmeta-wasm");
const wasmOutDirFromCrate = "../web/generated/postmeta-wasm";
const wasmBinaryName = "postmeta_wasm_bg.wasm";

function decode(bytes: Uint8Array): string {
  return decoder.decode(bytes).trim();
}

async function runCommand(
  command: string,
  args: string[],
  cwd: string,
  env: Record<string, string> = {},
): Promise<void> {
  const result = await new Deno.Command(command, {
    args,
    cwd,
    env,
    stdout: "piped",
    stderr: "piped",
  }).output();

  if (result.code !== 0) {
    const stderr = decode(result.stderr);
    const stdout = decode(result.stdout);
    const output = [stdout, stderr].filter((text) => text.length > 0).join("\n");
    throw new Error(
      `Command failed: ${command} ${args.join(" ")}\n${output}`,
    );
  }
}

async function optimizeWasmIfAvailable(wasmPath: string): Promise<void> {
  try {
    const version = await new Deno.Command("wasm-opt", {
      args: ["--version"],
      stdout: "piped",
      stderr: "piped",
    }).output();

    if (version.code !== 0) {
      console.warn("wasm-opt is unavailable; skipping post-build optimization.");
      return;
    }
  } catch (error) {
    if (error instanceof Deno.errors.NotFound) {
      console.warn("wasm-opt is not installed; skipping post-build optimization.");
      return;
    }
    throw error;
  }

  await runCommand(
    "wasm-opt",
    ["-Oz", wasmPath, "-o", wasmPath],
    webDir,
  );
}

export async function buildWasm(): Promise<void> {
  await ensureDir(join(webDir, "generated"));
  await Deno.remove(generatedWasmDir, { recursive: true }).catch((error: unknown) => {
    if (!(error instanceof Deno.errors.NotFound)) {
      throw error;
    }
  });

  const rustFlags = [
    "-Copt-level=z",
    "-Ccodegen-units=1",
    "-Cpanic=abort",
    "-Cstrip=symbols",
  ].join(" ");

  const env = {
    RUSTFLAGS: rustFlags,
    CARGO_PROFILE_RELEASE_OPT_LEVEL: "z",
    CARGO_PROFILE_RELEASE_CODEGEN_UNITS: "1",
    CARGO_PROFILE_RELEASE_STRIP: "symbols",
    CARGO_PROFILE_RELEASE_PANIC: "abort",
  };

  console.log("Building WASM module...");
  await runCommand(
    "wasm-pack",
    [
      "build",
      "--target",
      "web",
      "--release",
      "--no-opt",
      "--out-dir",
      wasmOutDirFromCrate,
      "--out-name",
      "postmeta_wasm",
    ],
    crateDir,
    env,
  );

  const wasmPath = join(generatedWasmDir, wasmBinaryName);
  await Deno.stat(wasmPath);

  await optimizeWasmIfAvailable(wasmPath);
  console.log(`WASM generated at ${generatedWasmDir}`);
}

if (import.meta.main) {
  await buildWasm();
}
