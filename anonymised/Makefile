.PHONY: all

all: pure-esop24-docker.tar.gz

pure-esop24-docker.tar.gz: Dockerfile
	DOCKER_BUILDKIT=0 docker build --pull --no-cache --squash -t pure-esop24 .
	docker save pure-esop24 | gzip > $@

