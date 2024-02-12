#!/usr/bin/env bash
set -e
# A small wrapper around TLC
# Add .ciignore file in a directory to ignore it.

tlc="java -Dtlc2.TLC.stopAfter=180 \
  -Dtlc2.TLC.ide=Github \
  -Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff \
  -XX:+UseParallelGC \
  -cp /tmp/tla2tools.jar:/tmp/CommunityModules-deps.jar tlc2.TLC \
  -workers auto \
  -lncheck final \
  -tool -modelcheck"

find . -mindepth 1 -maxdepth 1 -type d '!' -exec test -e "{}/.ciignore" ';' -print | grep -v ".git" | while read -r dir; do
  echo "Running $dir"
  cd $dir
  cfg_file=$(find "." -maxdepth 1 -type f -name "*.cfg" -print -quit)
  tla_file=${cfg_file/.cfg/.tla}
  ($tlc -config "$cfg_file" "$tla_file")
  cd ../
  echo "Finished checking $dir"
done
echo "Completed successfully."
