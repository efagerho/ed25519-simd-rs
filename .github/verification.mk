# Each audit writes to its own directory. The ZIP benchmark retains the decoder symbol.
routines := pow2 double4 cached-add scalar
linked_checks := $(addsuffix -conformance,$(routines))
timed = /usr/bin/time -f '$@ elapsed %E'
export XED_KIT := $(RUNNER_TEMP)/xed-kit

.PHONY: dalek-recompress dalek-recompress-mutations decompress-r decompress-r-mutations full-ladder stage-round stage-round-mutations radix16 radix16-mutations verify certificates ladder-mutations ladder torsion torsion-mutations small-order small-order-mutations pow2-z3 xed-kit fixed-conformance \
        $(routines) $(linked_checks) cached-add-mutations scalar-mutations

verify: dalek-recompress-mutations decompress-r-mutations full-ladder stage-round-mutations radix16-mutations ladder-mutations certificates cached-add-mutations $(linked_checks) \
        scalar-mutations torsion-mutations small-order-mutations fixed-conformance pow2-z3

certificates:
	$(timed) cargo build --locked --release \
	  --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add,verify-asm-scalar \
	  --lib --target x86_64-unknown-linux-gnu

pow2-z3:
	$(timed) /usr/bin/python3 -B verification/crate/pow2/check.py "$(RELEASE_ELF)"

audit_driver := audit.py
pow2: audit_driver := coq_proof.py
$(routines):
	$(timed) /usr/bin/python3 -B verification/crate/$(subst -,_,$@)/$(audit_driver) "$(RELEASE_ELF)" \
	  --output "$(RUNNER_TEMP)/$@-audit" --cases "$(RUNNER_TEMP)/$@-cases.jsonl" --seed 42

ladder:
	$(timed) /usr/bin/python3 -B verification/crate/ladder_step/audit.py "$(RELEASE_ELF)" \
	  --output "$(RUNNER_TEMP)/ladder-step-audit"

ladder-mutations: full-ladder
	$(timed) /usr/bin/python3 -B verification/crate/ladder_step/mutations.py "$(RELEASE_ELF)" \
	  --audit "$(RUNNER_TEMP)/full-ladder-audit"

torsion:
	$(timed) python3 -B verification/crate/torsion/audit.py "$(RELEASE_ELF)" \
	  --output "$(RUNNER_TEMP)/torsion-audit"

torsion-mutations: torsion
	$(timed) python3 -B verification/crate/torsion/mutations.py "$(RELEASE_ELF)" \
	  --audit "$(RUNNER_TEMP)/torsion-audit"

small-order:
	$(timed) python3 -B verification/crate/small_order/audit.py "$(RELEASE_ELF)" \
	  --output "$(RUNNER_TEMP)/small-order-audit"

small-order-mutations: small-order
	$(timed) python3 -B verification/crate/small_order/mutations.py "$(RELEASE_ELF)" \
	  --audit "$(RUNNER_TEMP)/small-order-audit"

cached-add-mutations scalar-mutations: %-mutations:
	$(timed) python3 -B verification/crate/$(subst -,_,$*)/mutations.py \
	  --output "$(RUNNER_TEMP)/$@" $(if $(filter all,$(MACHINE_BACKEND)),--native)

xed-kit:
	$(timed) verification/machine/tests/xed/build-kit.sh "$(XED_KIT)"

fixed-conformance: xed-kit
	$(timed) python3 -B verification/machine/tests/run.py --backend "$(MACHINE_BACKEND)" \
	  --report "$(RUNNER_TEMP)/fixed-report.json" --failure "$(RUNNER_TEMP)/fixed-failure.json"

$(linked_checks): %-conformance: % xed-kit
	$(timed) python3 -B verification/machine/tests/run.py --backend "$(MACHINE_BACKEND)" --cases "$(RUNNER_TEMP)/$*-cases.jsonl" \
	  --report "$(RUNNER_TEMP)/$*-report.json" --failure "$(RUNNER_TEMP)/$*-failure.json"

radix16:
	$(timed) python3 -B verification/crate/radix16/audit.py "$(RELEASE_ELF)" \
		--output "$(RUNNER_TEMP)/radix16-audit"

radix16-mutations: radix16
	$(timed) python3 -B verification/crate/radix16/mutations.py "$(RELEASE_ELF)" \
		--audit "$(RUNNER_TEMP)/radix16-audit"

stage-round:
	$(timed) python3 -B verification/crate/stage_round/audit.py "$(RELEASE_ELF)" \
		--output "$(RUNNER_TEMP)/stage-round-audit"

stage-round-mutations: full-ladder
	$(timed) python3 -B verification/crate/stage_round/mutations.py "$(RELEASE_ELF)" \
		--audit "$(RUNNER_TEMP)/full-ladder-audit"

full-ladder:
	$(timed) python3 -B verification/crate/full_ladder/audit.py "$(RELEASE_ELF)" \
	  --output "$(RUNNER_TEMP)/full-ladder-audit"

decompress-r:
	$(timed) python3 -B verification/crate/decompress_r/audit.py "$(ZIP_ELF)" \
		--output "$(RUNNER_TEMP)/decompress-r-audit"

decompress-r-mutations: decompress-r
	$(timed) python3 -B verification/crate/decompress_r/mutations.py "$(ZIP_ELF)" \
		--audit "$(RUNNER_TEMP)/decompress-r-audit"

dalek-recompress:
	$(timed) python3 -B verification/crate/dalek_recompress/audit.py "$(DALEK_ELF)" \
	  --output "$(RUNNER_TEMP)/dalek-recompress-audit"

dalek-recompress-mutations: dalek-recompress
	$(timed) python3 -B verification/crate/dalek_recompress/mutations.py "$(DALEK_ELF)" \
	  --audit "$(RUNNER_TEMP)/dalek-recompress-audit"
