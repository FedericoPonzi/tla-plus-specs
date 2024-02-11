#!/usr/bin/env bash
# A small wrapper around TLC
TLC_PATH=$1

TLC_COMMAND="java -Dtlc2.TLC.stopAfter=180 -Dtlc2.TLC.ide=Github -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff -cp tla2tools.jar tlc2.TLC -workers auto -lncheck final -tool -deadlock"
find . -mindepth 1 -maxdepth 1 -type d '!' -exec test -e "{}/.ciignore" ';' -print | grep -v ".git" | xargs -n 1 "$TLC_COMMAND"


