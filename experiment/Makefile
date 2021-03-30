run: TPaxos

TPaxos:
	@mkdir -p out; for i in Eager_config/*.ini; do echo $$i; j=$${i%ini}out; j=out/$${j#config/}; python3 tlcwrapper.py $$i 2>&1; echo; done

clean:
	find TPaxos -mindepth 1 -maxdepth 1 -type d -exec rm -rf \{\} \;; rm -rf out
