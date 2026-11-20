From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI Kernels Lane Control Bounds KernelCalls.
Import ListNotations. Open Scope Z_scope.
Inductive site := AB | ProductsAB | ProductCD | FG | EH | XZ | YT.
Definition site_kernel site (full affine:bool) := match site with
 | AB=>PrepareAB | ProductsAB=>Independent | ProductCD=>if affine then Single else Independent
 | FG=>PrepareFG | EH=>PrepareEH | XZ=>Pair | YT=>if full then Pair else Single end.
Definition site_index site (full affine:bool) := match site with
 | AB=>4%nat | ProductsAB=>5%nat | ProductCD=>if affine then 17%nat else 18%nat
 | FG=>19%nat | EH=>30%nat | XZ=>42%nat | YT=>if full then 55%nat else 54%nat end.
Definition site_bases site := match site with
 | AB=>[(7%nat,(point,0))] | ProductsAB=>[(8%nat,(cached,0))]
 | ProductCD=>[(8%nat,(cached,640))] | FG=>[] | EH=>[(9%nat,(scratch,0))]
 | XZ=>[(8%nat,(scratch,640))] | YT=>[(8%nat,(scratch,320))] end.
Definition all_sites := [AB;ProductsAB;ProductCD;FG;EH;XZ;YT].
Lemma calls_checked j full affine : forallb(fun site=>
 kernel_inputs(site_kernel site full affine)
 (prefix_bounds j full affine(site_index site full affine))(site_bases site))all_sites=true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Lemma site_checked j full affine site : kernel_inputs(site_kernel site full affine)
 (prefix_bounds j full affine(site_index site full affine))(site_bases site)=true.
Proof. pose proof(calls_checked j full affine)as H;rewrite forallb_forall in H.
 apply H;destruct site;cbn [all_sites In];intuition. Qed.
Lemma site_event full affine site : nth_error(expected_path full affine)(site_index site full affine)=
 Some(Evaluate(kernel_id(site_kernel site full affine))(site_bases site)).
Proof. destruct site,full,affine;vm_compute;reflexivity. Qed.
Theorem site_correct j full affine s site start : lane_words s ->input_bounds affine s ->
 In start(output_starts(site_kernel site full affine)) ->
 represents(limbs(rfield(prefix_state j full affine(S(site_index site full affine))s)start))
 (target_value(site_kernel site full affine)(registers(prefix_state j full affine(site_index site full affine)s))
 (fun i=>lane_load(prefix_state j full affine(site_index site full affine)s)(site_bases site)
 (KernelInterface.load_base(site_kernel site full affine))(64*Z.of_nat i))start).
Proof. intros;apply call_correct;auto using site_checked,site_event. Qed.
