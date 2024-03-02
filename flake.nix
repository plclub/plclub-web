{
  description = "The static site compiler for the UPenn PL Club";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
  };
  outputs = { self, nixpkgs }: {
    packages.x86_64-linux.default =
      with import nixpkgs { system = "x86_64-linux"; };
      let alectryon-deps = with python310Packages; [ coq coqPackages.serapi alectryon myst-parser ];
      in stdenv.mkDerivation {
        nativeBuildInputs = [ ghc cabal-install zlib pkgconfig bibtex2html ] ++ alectryon-deps;
        name = "hello";
        src = self;
      };
    devShells.x86_64-linux.default =
      let pkgs = import nixpkgs { system = "x86_64-linux"; };
          alectryon-deps = with pkgs;
            [ coq
              coqPackages.serapi
              python310Packages.alectryon
              python310Packages.myst-parser
            ];
          other-deps = with pkgs;
            [ zlib
              pkgconfig
              bibtex2html
            ];
          haskell-deps = with pkgs.haskellPackages;
            [ cabal2nix
              cabal-install
            ];
      in pkgs.haskellPackages.shellFor {
        packages = ps: [ ];
        buildInputs = haskell-deps ++ alectryon-deps ++ other-deps;
      };
  };
}
