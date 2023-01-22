.PHONY: test-output

test-output:
	go run . > $@
