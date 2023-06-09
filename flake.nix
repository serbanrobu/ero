{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { flake-utils, nixpkgs, rust-overlay, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
      in
      {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            bacon
            cargo-watch
            evcxr
            openssl
            pkg-config
            podman
            podman-compose
            (rust-bin.selectLatestNightlyWith (toolchain: toolchain.default.override {
              extensions = [ "rust-analyzer" "rust-src" ];
            }))
            sqlx-cli
          ];
          shellHook = ''
            # Import environment variables
            eval "$(grep -v '^#' ./.env | xargs)"

            export DATABASE_URL="postgres://''${DB_USER}:''${DB_PASSWORD}@localhost:''${DB_PORT}/''${DB_NAME}"
          '';
        };
      }
    );
}
