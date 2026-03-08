{
  description = "Meld - Static WebAssembly component fusion";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachSystem [
      "x86_64-linux"
      "aarch64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
    ] (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        # Rust 1.85.0 stable with wasm32-wasip2 target
        rustToolchain = pkgs.rust-bin.stable."1.85.0".default.override {
          targets = [ "wasm32-wasip2" ];
        };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # Rust toolchain (1.85.0 + wasm32-wasip2)
            rustToolchain

            # Build system
            pkgs.bazel_7

            # WebAssembly tools
            pkgs.wasmtime
            pkgs.wit-bindgen # wit-bindgen-cli for test fixture generation

            # General development
            pkgs.pkg-config
            pkgs.openssl
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.darwin.apple_sdk.frameworks.Security
            pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
            pkgs.libiconv
          ];

          # Bazel needs these to find the C/C++ toolchain
          env = {
            RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";
          };

          shellHook = ''
            echo "meld dev shell"
            echo "  rust: $(rustc --version)"
            echo "  cargo: $(cargo --version)"
            echo "  bazel: $(bazel --version 2>/dev/null | head -1)"
            echo "  wasmtime: $(wasmtime --version 2>/dev/null)"
          '';
        };

        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "meld";
          version = "0.2.0";
          src = pkgs.lib.cleanSource ./.;
          cargoLock.lockFile = ./Cargo.lock;

          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.openssl ]
            ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              pkgs.darwin.apple_sdk.frameworks.Security
              pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
              pkgs.libiconv
            ];

          # Only build the CLI binary
          cargoBuildFlags = [ "--package" "meld-cli" ];

          # Skip tests in the Nix build (they need wasm fixtures)
          doCheck = false;

          meta = {
            description = "Static WebAssembly component fusion tool";
            homepage = "https://github.com/pulseengine/meld";
            license = pkgs.lib.licenses.asl20;
            mainProgram = "meld";
          };
        };
      }
    );
}
