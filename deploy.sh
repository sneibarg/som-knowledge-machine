#!/bin/sh
set -eu

cd -- "$(dirname -- "$0")"
version=$(tr -d '\r' < VERSION)
case "$version" in
    ''|*[!a-zA-Z0-9._-]*)
        printf '%s\n' 'VERSION must contain a single Maven version.' >&2
        exit 1
        ;;
    *-SNAPSHOT) ;;
    *) set -- -Prelease "$@" ;;
esac

clojure -T:build jar
exec mvn -B -f maven-deploy.xml deploy:deploy-file \
    "-Dfile=target/som-knowledge-machine-$version.jar" "$@"
