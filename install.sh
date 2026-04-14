#!/bin/sh
set -eu

REPO="dylantf/saga"
INSTALL_DIR="${SAGA_HOME:-$HOME/.saga}/bin"

main() {
    platform=$(detect_platform)
    if [ -z "$platform" ]; then
        echo "Error: unsupported platform $(uname -s) $(uname -m)" >&2
        exit 1
    fi

    check_dependencies

    version=$(get_version "${1:-}")
    url="https://github.com/${REPO}/releases/download/${version}/saga-${platform}.tar.gz"

    echo "Installing saga ${version} (${platform})"

    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT

    echo "Downloading ${url}"
    if command -v curl > /dev/null; then
        curl -fsSL "$url" -o "$tmpdir/saga.tar.gz"
    elif command -v wget > /dev/null; then
        wget -qO "$tmpdir/saga.tar.gz" "$url"
    else
        echo "Error: curl or wget required" >&2
        exit 1
    fi

    mkdir -p "$INSTALL_DIR"
    tar xzf "$tmpdir/saga.tar.gz" -C "$INSTALL_DIR"
    chmod +x "$INSTALL_DIR/saga" "$INSTALL_DIR/saga-lsp"

    echo "Installed saga to ${INSTALL_DIR}/saga"
    echo "Installed saga-lsp to ${INSTALL_DIR}/saga-lsp"

    if ! echo "$PATH" | tr ':' '\n' | grep -qx "$INSTALL_DIR"; then
        echo ""
        echo "Add saga to your PATH by adding this to your shell profile:"
        echo ""
        echo "  export PATH=\"${INSTALL_DIR}:\$PATH\""
    fi
}

detect_platform() {
    os=$(uname -s)
    arch=$(uname -m)

    case "$os" in
        Linux)
            case "$arch" in
                x86_64) echo "linux-x86_64" ;;
                *) return 1 ;;
            esac
            ;;
        Darwin)
            case "$arch" in
                x86_64) echo "macos-x86_64" ;;
                arm64)  echo "macos-aarch64" ;;
                *) return 1 ;;
            esac
            ;;
        *) return 1 ;;
    esac
}

get_version() {
    if [ -n "${1:-}" ]; then
        echo "$1"
        return
    fi

    if command -v curl > /dev/null; then
        curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" \
            | sed -n 's/.*"tag_name": *"\([^"]*\)".*/\1/p'
    elif command -v wget > /dev/null; then
        wget -qO- "https://api.github.com/repos/${REPO}/releases/latest" \
            | sed -n 's/.*"tag_name": *"\([^"]*\)".*/\1/p'
    fi
}

check_dependencies() {
    missing=""

    if ! command -v erl > /dev/null; then
        missing="${missing}  - erl (Erlang/OTP runtime)\n"
    fi
    if ! command -v erlc > /dev/null; then
        missing="${missing}  - erlc (Erlang compiler)\n"
    fi

    if [ -n "$missing" ]; then
        echo "Warning: saga requires Erlang/OTP. Missing commands:"
        printf "%b" "$missing"
        echo ""
        echo "Install Erlang/OTP from https://www.erlang.org/downloads"
        echo "  or via your package manager (e.g. brew install erlang)"
        echo ""
    fi
}

main "$@"
