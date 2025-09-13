#!/bin/sh
# Install Lean 4 via elan toolchain manager

echo "Installing Lean 4 via elan..."

# Detect OS
OS=$(uname -s)
ARCH=$(uname -m)

case "$OS" in
    FreeBSD)
        echo "FreeBSD detected. Checking for Lean 4 in ports..."

        # Try to install via pkg first
        if command -v pkg >/dev/null 2>&1; then
            echo "Attempting to install Lean 4 via pkg..."
            if sudo pkg install -y lean4 2>/dev/null; then
                echo "Lean 4 installed via FreeBSD pkg"
            else
                echo "Lean 4 not available in FreeBSD pkg, trying alternative..."

                # Try to use Linux binary with compat layer
                echo "Installing Linux compatibility layer..."
                sudo pkg install -y linux-c7-libc

                # Download Linux binary
                echo "Downloading Linux elan binary..."
                mkdir -p "$HOME/.local/bin"
                curl -L https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz -C "$HOME/.local/bin"

                # Add to PATH
                export PATH="$HOME/.local/bin:$PATH"
                echo 'export PATH="$HOME/.local/bin:$PATH"' >> "$HOME/.profile"
            fi
        fi
        ;;
    Linux|Darwin)
        # Download and install elan (Lean version manager)
        if ! command -v elan >/dev/null 2>&1; then
            echo "Downloading and installing elan..."
            curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

            # Source the environment to make elan available
            if [ -f "$HOME/.elan/env" ]; then
                . "$HOME/.elan/env"
            fi
        else
            echo "elan is already installed"
        fi

        # Update elan and install latest stable Lean 4
        echo "Updating elan and installing latest Lean 4..."
        elan self update
        elan toolchain install stable
        elan default stable
        ;;
    *)
        echo "Unsupported OS: $OS"
        echo "Please install Lean 4 manually from https://leanprover.github.io/lean4/doc/quickstart.html"
        exit 1
        ;;
esac

# Verify installation
echo "Verifying Lean 4 installation..."

# Check various possible locations
LEAN_PATHS="/usr/local/bin/lean $HOME/.elan/bin/lean $HOME/.local/bin/lean"
LAKE_PATHS="/usr/local/bin/lake $HOME/.elan/bin/lake $HOME/.local/bin/lake"

LEAN_FOUND=false
LAKE_FOUND=false

for lean_path in $LEAN_PATHS; do
    if [ -x "$lean_path" ]; then
        echo "Found lean at: $lean_path"
        if "$lean_path" --version 2>/dev/null; then
            LEAN_FOUND=true
            break
        fi
    fi
done

for lake_path in $LAKE_PATHS; do
    if [ -x "$lake_path" ]; then
        echo "Found lake at: $lake_path"
        if "$lake_path" --version 2>/dev/null; then
            LAKE_FOUND=true
            break
        fi
    fi
done

if ! $LEAN_FOUND; then
    echo "Warning: lean command not working properly"
fi

if ! $LAKE_FOUND; then
    echo "Warning: lake command not working properly"
fi

echo "Lean 4 installation script complete!"
echo ""
echo "If lean/lake are not in your PATH, try:"
echo "  source ~/.elan/env                    # for elan installation"
echo "  export PATH=\"\$HOME/.local/bin:\$PATH\"  # for local installation"
echo "  rehash                                # for some shells"