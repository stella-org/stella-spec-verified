{
  inputs = {
    fstar.url = "github:FStarLang/FStar/v2026.10.11";
    nixpkgs.follows = "fstar/nixpkgs";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, fstar, nixpkgs, utils, purescript-overlay }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system; 
          overlays = [
            purescript-overlay.overlays.default
          ];
        };
        fstar-pkg = fstar.packages.${system}.fstar;
        z3-pkg = fstar.packages.${system}.z3;

        fstarCmd = pkgs.writeShellScriptBin "fstar" ''
          exec ${fstar-pkg}/bin/fstar.exe \
            --include ${fstar-pkg}/lib/fstar \
            --cache_checked_modules \
            --cache_dir .fstar-cache \
            "$@"
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            fstar-pkg
            z3-pkg
            fstarCmd
          ] ++ (with pkgs;
          [ purs 
            spago-unstable
            purs-tidy-bin.purs-tidy-0_10_0
            purs-backend-es
            nodejs_24
            pnpm
          ]);

        };
      });
}
