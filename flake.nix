{
  description = "Saga: a functional language with algebraic effects, compiling to BEAM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        cargoToml = builtins.fromTOML (builtins.readFile ./Cargo.toml);

        runtimeDeps = [
          pkgs.erlang
          pkgs.rebar3
        ];

        saga = pkgs.rustPlatform.buildRustPackage {
          pname = "saga";
          version = cargoToml.package.version;
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          doCheck = false;

          nativeBuildInputs = [
            pkgs.pkg-config
            pkgs.makeBinaryWrapper
          ];
          buildInputs = [
            pkgs.openssl
          ];

          postInstall = ''
            wrapProgram $out/bin/saga \
              --prefix PATH : ${pkgs.lib.makeBinPath runtimeDeps}
          '';

          meta = with pkgs.lib; {
            description = "Functional language with algebraic effects, compiling to BEAM";
            homepage = "https://github.com/dylantf/saga";
            license = licenses.gpl3Only;
            mainProgram = "saga";
          };
        };
      in
      {
        packages = {
          default = saga;
          saga = saga;
        };

        apps.default = {
          type = "app";
          program = "${saga}/bin/saga";
        };

        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.rustc
            pkgs.cargo
            pkgs.gcc
            pkgs.pkg-config
            pkgs.rust-analyzer
            pkgs.rustfmt
            pkgs.clippy
          ]
          ++ runtimeDeps;

          buildInputs = [
            pkgs.bashInteractive
            pkgs.openssl
          ];

          RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";
        };
      }
    );
}
