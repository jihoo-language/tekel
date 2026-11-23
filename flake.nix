{
  description = "Tekel";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-26.05";

  outputs = { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      package = pkgs: pkgs.rustPlatform.buildRustPackage {
        pname = "tekel";
        version = "0.1.0";
        src = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./Cargo.lock
            ./Cargo.toml
            ./examples
            ./src
            ./tests
          ];
        };
        cargoLock.lockFile = ./Cargo.lock;
        meta = {
          description = "Tekel: every function weighed";
          license = pkgs.lib.licenses.asl20;
          mainProgram = "tekel";
        };
      };
    in
    {
      packages = forSystems (pkgs: { default = package pkgs; });
      apps = forSystems (pkgs: {
        default = {
          type = "app";
          program = pkgs.lib.getExe (package pkgs);
          meta.description = "Weigh a Tekel program";
        };
      });
      devShells = forSystems (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [ cargo rustc rustfmt clippy ];
        };
      });
      checks = forSystems (pkgs: { default = package pkgs; });
    };
}
