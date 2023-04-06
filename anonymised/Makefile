.PHONY: all

all: pure-pldi23-docker.tar.gz

pure-pldi23-docker.tar.gz: Dockerfile
	docker build --pull --no-cache --squash -t pure-pldi23 .
	docker save pure-pldi23 | gzip > $@

