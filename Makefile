.PHONY: test-output

test-output:
	-go run . > $@ 2>&1
