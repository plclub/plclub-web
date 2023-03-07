{
  description = "The static site compiler for the UPenn PL Club";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.11;
  };
  outputs = { self, nixpkgs }: {
    packages.x86_64-linux.default =
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation {
        nativeBuildInputs = [ ghc cabal-install zlib pkgconfig bibtex2html ];
        name = "hello";
        src = self;
        buildPhase = "cabal build";
      };
  };
}
