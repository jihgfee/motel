{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/43080df7e44a5873d9973e8d9de853e7097d6a2e";
    flake-utils.url = "github:numtide/flake-utils";

    stdpp-dev-src = {
      url = "git+https://git@gitlab.mpi-sws.org/iris/stdpp?rev=22033707c106f1e584640ec828e77fe4c13a9cd3";
      flake = false;
    };

    iris-dev-src = {
      url = "git+https://gitlab.mpi-sws.org/iris/iris?ref=robbert/elim_modal_modality&rev=8e5e08bca0d33135a0d1a520ac3b6230248037ff";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, stdpp-dev-src, iris-dev-src, ... }: let

    stdpp-dev-d = { lib, builder, rocq_coq_pkgs }: builder rec {
      pname = "stdpp-dev";
      propagatedBuildInputs = with rocq_coq_pkgs; [ stdlib coq ];
      defaultVersion = "dev";

      release."dev" = {
        src = stdpp-dev-src.outPath;
      };
    };

    iris-dev-d = { lib, builder, rocq_coq_pkgs }: builder rec {
      pname = "iris-dev";
      propagatedBuildInputs = with rocq_coq_pkgs; [ stdlib stdpp-dev ];
      defaultVersion = "dev";

      release."dev" = {
        src = iris-dev-src.outPath;
      };
    };

    motel-d = { lib, builder, rocq_coq_pkgs }: builder rec {
      pname = "ltl";
      propagatedBuildInputs = with rocq_coq_pkgs; [
        stdlib
        iris-dev
        stdpp-dev
        coq # for coq_makefile / rocq makefile
      ];
      defaultVersion = "dev";
      release."dev" = {
        src = ./.;
      };
    };

  in flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ self.overlays.default ];
    };
    coqPkgs = pkgs.coqPackages_9_0;
  in {
    packages = rec {
      motel = coqPkgs.motel;
      default = motel;
    };

    devShells.default = pkgs.mkShell {
      buildInputs = [
        coqPkgs.stdlib
        coqPkgs.motel
      ];
    };
  }) // {
    overlays.default = final: prev: (
      prev.lib.mapAttrs (name: _:
        prev.${name}.overrideScope (self: _: {
          stdpp-dev = self.callPackage stdpp-dev-d { builder = self.mkRocqDerivation; rocq_coq_pkgs = prev.coqPackages_9_0 // self; };
          iris-dev  = self.callPackage iris-dev-d  { builder = self.mkRocqDerivation; rocq_coq_pkgs = prev.coqPackages_9_0 // self; };
          motel     = self.callPackage motel-d     { builder = self.mkRocqDerivation; rocq_coq_pkgs = prev.coqPackages_9_0 // self; };
        })
      ) {
        inherit (final) rocqPackages_9_0;
      } //
      prev.lib.mapAttrs (name: _:
        prev.${name}.overrideScope (self: _: {
          stdpp-dev = self.callPackage stdpp-dev-d { builder = self.mkCoqDerivation; rocq_coq_pkgs = self; };
          iris-dev  = self.callPackage iris-dev-d  { builder = self.mkCoqDerivation; rocq_coq_pkgs = self; };
          motel     = self.callPackage motel-d     { builder = self.mkCoqDerivation; rocq_coq_pkgs = self; };
        })
      ) {
        inherit (final) coqPackages_9_0;
      }
    );
  };
}
