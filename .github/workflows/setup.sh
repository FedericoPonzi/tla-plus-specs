#!/usr/bin/env bash

# Get TLA⁺ tools
wget -nv http://nightly.tlapl.us/dist/tla2tools.jar -P "/tmp"
# Get TLA⁺ community modules
wget -nv https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar \
    -P "/tmp"