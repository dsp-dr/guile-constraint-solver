#!/bin/sh
#!/bin/sh
# Install dependencies on FreeBSD

echo "Installing Z3 SMT solver..."
sudo pkg install -y z3

echo "Installing Guile 3.x if not present..."
sudo pkg install -y guile3

echo "Checking installations..."
z3 --version
guile --version
