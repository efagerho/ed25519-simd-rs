# Each audit writes to its own directory. The ZIP benchmark retains the decoder symbol.
routines := pow2 double4 cached-add scalar
linked_checks := $(addsuffix -conformance,$(routines))
timed = /usr/bin/time -f '$@ elapsed %E'
export XED_KIT := $(RUNNER_TEMP)/xed-kit

.PHONY: prepare-chunk prepare-chunk-mutations signature-scalar signature-scalar-mutations key-table key-table-mutations dalek-post-hash dalek-post-hash-mutations zip215 zip215-mutations dalek-recompress dalek-recompress-mutations decompress-r decompress-r-mutations full-ladder stage-round stage-round-mutations radix16 radix16-mutations verify certificates ladder-mutations ladder torsion torsion-mutations small-order small-order-mutations pow2-z3 xed-kit fixed-conformance \
        $(routines) $(linked_checks) cached-add-mutations scalar-mutations

verify: prepare-chunk-mutations signature-scalar-mutations key-table-mutations dalek-post-hash-mutations zip215-mutations dalek-recompress-mutations decompress-r-mutations full-ladder stage-round-mutations radix16-mutations ladder-mutations certificates cached-add-mutations $(linked_checks) \
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
	$(timed) /usr/bin/python3 -B verification/crate/ladder_step/mutations.py "$(ZIP_ELF)" \
	  --audit "$(RUNNER_TEMP)/full-ladder-audit"

torsion:
	$(timed) python3 -B verification/crate/torsion/audit.py "$(ZIP_ELF)" \
	  --output "$(RUNNER_TEMP)/torsion-audit"

torsion-mutations: torsion
	$(timed) python3 -B verification/crate/torsion/mutations.py "$(ZIP_ELF)" \
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
	$(timed) python3 -B verification/crate/radix16/audit.py "$(ZIP_ELF)" \
		--output "$(RUNNER_TEMP)/radix16-audit"

radix16-mutations: radix16
	$(timed) python3 -B verification/crate/radix16/mutations.py "$(ZIP_ELF)" \
		--audit "$(RUNNER_TEMP)/radix16-audit"

stage-round:
	$(timed) python3 -B verification/crate/stage_round/audit.py "$(RELEASE_ELF)" \
		--output "$(RUNNER_TEMP)/stage-round-audit"

stage-round-mutations: full-ladder
	$(timed) python3 -B verification/crate/stage_round/mutations.py "$(ZIP_ELF)" \
		--audit "$(RUNNER_TEMP)/full-ladder-audit"

full-ladder:
	$(timed) python3 -B verification/crate/full_ladder/audit.py "$(ZIP_ELF)" \
	  --output "$(RUNNER_TEMP)/full-ladder-audit"

key-table: full-ladder
	$(timed) python3 -B verification/crate/key_table/audit.py "$(ZIP_ELF)" \
		--output "$(RUNNER_TEMP)/key-table-audit" --dependencies "$(RUNNER_TEMP)"

key-table-mutations: key-table
	$(timed) python3 -B verification/crate/key_table/mutations.py "$(ZIP_ELF)" \
		--audit "$(RUNNER_TEMP)/key-table-audit"

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

zip215: full-ladder radix16 torsion decompress-r
	$(timed) python3 -B verification/crate/zip215/audit.py "$(ZIP_ELF)" \
		--output "$(RUNNER_TEMP)/zip215-audit" --dependencies "$(RUNNER_TEMP)" \
		--recompress-dependencies "$(RUNNER_TEMP)/zip215-callees"

zip215-mutations: zip215
	$(timed) python3 -B verification/crate/zip215/mutations.py "$(ZIP_ELF)" --audit "$(RUNNER_TEMP)/zip215-audit"

# Callee proofs bind absolute addresses and relative operands in this ELF.
dalek_dependencies := $(addprefix $(RUNNER_TEMP)/dalek-callees/,$(addsuffix -audit/manifest.json,radix16 full-ladder decompress-r))
$(dalek_dependencies): $(RUNNER_TEMP)/dalek-callees/%-audit/manifest.json:
	$(timed) python3 -B verification/crate/$(subst -,_,$*)/audit.py "$(DALEK_ELF)" --output "$(@D)"

dalek-post-hash: dalek-recompress $(dalek_dependencies)
	$(timed) python3 -B verification/crate/dalek_post_hash/audit.py "$(DALEK_ELF)" \
		--output "$(RUNNER_TEMP)/dalek-post-hash-audit" --dependencies "$(RUNNER_TEMP)/dalek-callees" \
		--recompress-dependencies "$(RUNNER_TEMP)"

dalek-post-hash-mutations: dalek-post-hash
	$(timed) python3 -B verification/crate/dalek_post_hash/mutations.py "$(DALEK_ELF)" --audit "$(RUNNER_TEMP)/dalek-post-hash-audit"

signature-scalar:
	$(timed) python3 -B verification/crate/signature_scalar/audit.py "$(ZIP_ELF)" \
		--output "$(RUNNER_TEMP)/signature-scalar-audit"

signature-scalar-mutations: signature-scalar
	$(timed) python3 -B verification/crate/signature_scalar/mutations.py "$(ZIP_ELF)" \
		--audit "$(RUNNER_TEMP)/signature-scalar-audit"

prepare_deps := $(RUNNER_TEMP)/dalek-callees
$(prepare_deps)/signature-scalar-audit/manifest.json:
	$(timed) python3 -B verification/crate/signature_scalar/audit.py "$(DALEK_ELF)" --output "$(@D)"

$(prepare_deps)/key-table-audit/manifest.json: $(prepare_deps)/full-ladder-audit/manifest.json
	$(timed) python3 -B verification/crate/key_table/audit.py "$(DALEK_ELF)" --output "$(@D)" \
		--dependencies "$(prepare_deps)"

prepare-chunk: dalek-post-hash $(addprefix $(prepare_deps)/,signature-scalar-audit/manifest.json key-table-audit/manifest.json)
	$(timed) python3 -B verification/crate/prepare_chunk/audit.py "$(DALEK_ELF)" \
		--output "$(RUNNER_TEMP)/prepare-chunk-audit" --dependencies "$(prepare_deps)" \
		--dalek-dependencies "$(RUNNER_TEMP)"

prepare-chunk-mutations: prepare-chunk
	$(timed) python3 -B verification/crate/prepare_chunk/mutations.py "$(DALEK_ELF)" \
		--audit "$(RUNNER_TEMP)/prepare-chunk-audit"
