# =============================================================================
# agda-lattices: Nix flake
#
# File: flake.nix
#
# `nix develop` drops you in a shell with exactly the Agda, standard library,
# and agda-algebras this library is checked against.
#
# Pinning:
#
#   +  agda-algebras is a flake input, pinned in its URL and by flake.lock at
#      commit b4d0ab6c of its master branch.
#   +  The Agda is the one agda-algebras exports (`packages.<system>.default`):
#      a pre-release Agda 2.9.0 built from agda/agda by Agda's own flake, with
#      the standard library 2.3 patched to check under it.  Neither comes from
#      nixpkgs; agda-algebras' flake pins both, so the pin above fixes the
#      library, the compiler and the standard library together.  Building that
#      Agda from source takes about an hour; the public Cachix cache
#      `formalverification` holds it (see the README).
#   +  nixpkgs follows agda-algebras' own pin and supplies the rest of the
#      shell: make, git, and the Python of the documentation site (MkDocs,
#      Material at a stated version, and the plugins; see below).
#
# Library resolution:
#
#   +  Agda writes interface files beside a library's .agda-lib, and the Nix
#      store is read-only, so the shell copies the pinned agda-algebras
#      sources to .deps/agda-algebras (once per pin) and registers that copy.
#      To use another copy (one whose interfaces are already built, say),
#      enter the shell with AGDA_ALGEBRAS_DIR set to its root.
#   +  The shell writes a project-local AGDA_DIR (.agda/), so nothing in the
#      user's Agda configuration directory is consulted.  The standard
#      library's .agda-lib is read from the exported Agda environment's own
#      library file (its `libraryFile` attribute), so this flake never names
#      the standard library's store path or version itself.
#   +  The wrapper at .agda/bin/agda execs the environment's store path, never
#      `command -v agda`, which can resolve to the wrapper itself and loop.
#
# This flake needs Nix 2.28 or later, as agda-algebras' does: the agda/agda
# tree it locks holds empty directories that an older Nix drops when hashing.
# =============================================================================
{
  description = "agda-lattices: lattice theory in Agda, on top of the Agda Universal Algebra Library";

  inputs = {
    agda-algebras.url = "github:ualib/agda-algebras/b4d0ab6cd9a6e32f28857bd5014bbacaa284bb35";
    nixpkgs.follows = "agda-algebras/nixpkgs";
  };

  outputs = { self, nixpkgs, agda-algebras }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          f { inherit system; pkgs = import nixpkgs { inherit system; }; });

      # The Agda environment agda-algebras exports: Agda 2.9.0 with the
      # patched standard library 2.3 registered in its own library file.
      mkAgdaEnv = system: agda-algebras.packages.${system}.default;

      # The documentation site's Python: MkDocs, Material and the plugins the
      # pipeline uses (mkdocs.yml).  One withPackages environment, since two
      # on the same PATH shadow each other rather than merge.  `make site`
      # and `make site-full` run in it.
      #
      # Material is pinned at the version agda-algebras' site pins, so that
      # the theme files copied from that site (docs/stylesheets/, overrides/)
      # render here as they do there, and so that `nix flake update` cannot
      # move the theme as a side effect.  To move it, change materialVersion
      # and materialHash together, after agda-algebras has moved (`nix store
      # prefetch-file` on the sdist URL prints the hash).  The PyPI sdist
      # carries the prebuilt `material/` tree, so the override is a
      # pure-Python build of seconds.
      materialVersion = "9.7.6";
      materialHash = "sha256-AL3eUFdPd20yixhi/mXa6vWB7DCb0VD3v/NFoJjGSmk=";
      mkMaterial = p: p.mkdocs-material.overridePythonAttrs (_: {
        version = materialVersion;
        src = p.fetchPypi {
          pname = "mkdocs_material";
          version = materialVersion;
          hash = materialHash;
        };
      });

      mkPythonEnv = pkgs: pkgs.python3.withPackages (p: [
        p.mkdocs                  # static-site generator
        (mkMaterial p)            # Material theme, pinned above
        p.mkdocs-gen-files        # mount src/**/*.lagda.md as site pages
        p.mkdocs-literate-nav     # the module tree from a generated SUMMARY.md
        p.mkdocs-section-index    # clickable section pages (the barrels)
        p.pymdown-extensions      # snippets (docs/_links.md on every page)
      ]);

      # Project-local AGDA_DIR, the agda-algebras copy, and an agda wrapper
      # that passes --library-file again after the Nix wrapper's own (Agda's
      # last-flag-wins rule), with --no-default-libraries so a user's own
      # defaults file cannot contribute.
      mkAgdaShellSetup = agdaEnv: ''
        ROOT="$PWD"
        if command -v git >/dev/null 2>&1 && git rev-parse --show-toplevel >/dev/null 2>&1; then
          ROOT="$(git rev-parse --show-toplevel)"
        fi

        export AGDA_DIR="$ROOT/.agda"
        mkdir -p "$AGDA_DIR"

        if [ -n "''${AGDA_ALGEBRAS_DIR:-}" ]; then
          ALGEBRAS="$AGDA_ALGEBRAS_DIR"
        else
          ALGEBRAS="$ROOT/.deps/agda-algebras"
          if [ "$(cat "$ALGEBRAS/.source" 2>/dev/null)" != "${agda-algebras}" ]; then
            rm -rf "$ALGEBRAS"
            mkdir -p "$ALGEBRAS"
            cp "${agda-algebras}/agda-algebras.agda-lib" "$ALGEBRAS/"
            cp -r "${agda-algebras}/src" "$ALGEBRAS/"
            chmod -R u+w "$ALGEBRAS"
            echo "${agda-algebras}" > "$ALGEBRAS/.source"
          fi
        fi
        export ALGEBRAS

        {
          cat "${agdaEnv.libraryFile}"
          echo "$ALGEBRAS/agda-algebras.agda-lib"
          echo "$ROOT/agda-lattices.agda-lib"
        } > "$AGDA_DIR/libraries"
        echo "standard-library" > "$AGDA_DIR/defaults"

        mkdir -p "$AGDA_DIR/bin"
        cat > "$AGDA_DIR/bin/agda" <<EOF
#!/usr/bin/env bash
exec "${agdaEnv}/bin/agda" \\
  --no-default-libraries \\
  --library-file "$AGDA_DIR/libraries" \\
  --library standard-library \\
  --library agda-algebras \\
  --library agda-lattices \\
  "\$@"
EOF
        chmod +x "$AGDA_DIR/bin/agda"
        export PATH="$AGDA_DIR/bin:$PATH"
      '';
    in {
      formatter = forAllSystems ({ pkgs, ... }: pkgs.nixpkgs-fmt);

      devShells = forAllSystems ({ system, pkgs }:
        let
          agdaEnv = mkAgdaEnv system;
          pythonEnv = mkPythonEnv pkgs;
          mkdocsVer = pkgs.python3Packages.mkdocs.version;
          materialVer = (mkMaterial pkgs.python3Packages).version;
        in {
          default = pkgs.mkShell {
            name = "agda-lattices-dev";

            packages = [
              agdaEnv
              pythonEnv
              pkgs.gnumake
              pkgs.git
            ];

            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";

            shellHook = ''
              ${mkAgdaShellSetup agdaEnv}

              echo ""
              echo "agda-lattices dev shell"
              echo "   Agda          : ${agdaEnv.version}    ($(agda --version 2>/dev/null | head -n1))"
              echo "   stdlib        : $(cat "${agdaEnv.libraryFile}")"
              echo "   agda-algebras : $ALGEBRAS"
              echo "   MkDocs        : ${mkdocsVer} + Material ${materialVer}  (make site / make site-full)"
              echo "   AGDA_DIR      : $AGDA_DIR"
              echo ""

              case "${agdaEnv.version}" in
                2.9.*) : ;;
                *) echo "warning: expected Agda 2.9.x, got ${agdaEnv.version}" ;;
              esac
            '';
          };
        });
    };
}
