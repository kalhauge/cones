{
  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixos-23.05;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , ...
    }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
    let
      packages = p: {
        "cones" = p.callCabal2nixWithOptions "cones" "${self}/cones" "" { };
        "conedec" = p.callCabal2nixWithOptions "conedec" "${self}/conedec" "" { };
      };
      overlays = final: prev: {
        haskellPackages = prev.haskellPackages.extend
          # (final.lib.composeExtensions (old.overrides or (_: _: { }))
          (p: _: packages p);
      };
      hpkgs = (import nixpkgs {
        inherit system;
        overlays = [ overlays ];
      }).haskellPackages;
    in
    rec {
      packages = {
        default = hpkgs.cones;
        cones = hpkgs.cones;
        conedec = hpkgs.conedec;
      };
      devShells.default = hpkgs.shellFor
        {
          name = "cones-shell";
          packages = p:
            [ p.cones p.conedec ];
          # doBenchmark = true;
          withHoogle = true;
          buildInputs = (with hpkgs; [
            cabal-install
            ghcid
            haskell-language-server
            hpack
            fourmolu
          ]);
        };
      devShells.conedec = hpkgs.shellFor
        {
          name = "conedec-shell";
          packages = p:
            [ p.conedec ];
          # doBenchmark = true;
          withHoogle = true;
          buildInputs = (with hpkgs; [
            cabal-install
            ghcid
            haskell-language-server
            hpack
            fourmolu
          ]);
        };
      overlays = overlays;
    });
}
