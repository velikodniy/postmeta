import React from "react";
import { createRoot } from "react-dom/client";

import { App } from "./App.tsx";
import "./styles.css";

const mountNode = document.getElementById("app");

if (mountNode) {
  createRoot(mountNode).render(
    <React.StrictMode>
      <App />
    </React.StrictMode>,
  );
}
