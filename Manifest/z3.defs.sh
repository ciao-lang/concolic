# 3rd-party package definition

# Package name
pkg_name="z3-4.7.1"

# Origin for binary distribution
function pkg_bin_origin() {
    # NOTE: Look at https://github.com/Z3Prover/z3/releases for releases
    # (there are 32-bit versions too)
    local baseurl="https://github.com/Z3Prover/z3/releases/download/$pkg_name"
    case "$CIAO_OS" in
	LINUX)
	    pkg_tarfile="$pkg_name""-x64-ubuntu-14.04.zip" ;;
	DARWIN)
	    pkg_tarfile="$pkg_name""-x64-osx-10.11.6.zip" ;;
	*)
	    echo "ERROR: Unsupported CIAO_OS=$CIAO_OS" 1>&2
	    exit 1
    esac
    pkg_url="$baseurl/$pkg_tarfile"
}

# Origin for source distribution
function pkg_src_origin() {
    local baseurl="https://github.com/Z3Prover/z3/archive"
    pkg_tarfile="$pkg_name""-src.tar.gz"
    pkg_url="$baseurl/$pkg_tarfile"
}

# Fixes for binary distribution
function pkg_fix_bin() {
    # Fix missing lib/ (point to bin)
    ln -s bin "$storedir/$pkg_name/lib"
    # Fix missing bin # TODO: do in a better way
    ln -s "../store/$pkg_name/bin/z3" "$THIRDPARTY/bin/z3"
}

# Build from source
function pkg_build() {
    # TODO: (Not tested)
    # LDFLAGS="-L$THIRDPARTY/lib" CPPFLAGS="-I$THIRDPARTY/include" LD_LIBRARY_PATH="$THIRDPARTY/lib" ./configure
    python scripts/mk_make.py --prefix="$storedir/$pkg_name"
    cd build
    make
}

# Install from source
function pkg_install() {
    make install
}

# Dynamic library name and files
pkg_lib=z3
# NOTE: (no lib name with version)
case "$CIAO_OS" in
    LINUX)
	pkg_libfile="libz3.so"
	pkg_libfileAct= #"libz3.so"
	;;
    DARWIN)
	pkg_libfile="libz3.dylib"
	pkg_libfileAct= #"libz3.dylib"
	;;
esac

