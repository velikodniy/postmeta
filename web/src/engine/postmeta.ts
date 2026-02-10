export interface CompileOutput {
  readonly svg: string;
  readonly diagnostics: string;
  readonly hasError: boolean;
}

interface WasmModule {
  default: (module?: URL | RequestInfo | Response | BufferSource | WebAssembly.Module) => Promise<unknown>;
  render_metapost: (source: string) => CompileOutput;
}

let modulePromise: Promise<WasmModule> | null = null;

async function loadModule(): Promise<WasmModule> {
  if (modulePromise) {
    return modulePromise;
  }

  modulePromise = (async () => {
    const moduleUrl = new URL(
      "../../generated/postmeta-wasm/postmeta_wasm.js",
      import.meta.url,
    );
    const wasmModule = (await import(moduleUrl.href)) as WasmModule;
    await wasmModule.default();
    return wasmModule;
  })();

  return modulePromise;
}

export async function compilePostMeta(source: string): Promise<CompileOutput> {
  try {
    const wasm = await loadModule();
    return wasm.render_metapost(source);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return {
      svg: "",
      diagnostics: `error ${message}`,
      hasError: true,
    };
  }
}
