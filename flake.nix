{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    tadni-platform.url = "github:tadni/platform";
  };

  outputs = { self, nixpkgs, tadni-platform }: let
    for-all-systems = f:
      nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-darwin"
      ] (system: f (import nixpkgs {
        inherit system;
        config.allowUnfree = true;
        overlays = [ tadni-platform.overlays.default ];
      }));
  in {
    devShells = for-all-systems (pkgs: let
      coqPackages = pkgs.coqPackages_8_20;
    in {
      default = pkgs.mkShell {
        shellHook = ''
          unset SOURCE_DATE_EPOCH
          export OCAMLPATH="$(find ${coqPackages.metacoq.template-coq} \
            -name site-lib -type d | head -1):$(find \
            ${coqPackages.coq.ocamlPackages.zarith} \
            -name site-lib -type d | head -1):$(find \
            ${coqPackages.coq.ocamlPackages.stdlib-shims} \
            -name site-lib -type d | head -1):$OCAMLPATH"
        '';
        buildInputs = 
          coqPackages.coq-lens.buildInputs;
        nativeBuildInputs = [
          coqPackages.metacoq.template-coq
          coqPackages.coq.ocamlPackages.zarith
          coqPackages.coq.ocamlPackages.stdlib-shims
        ];
      };
    });
  };
}
