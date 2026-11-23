#[cfg(not(feature = "verify-asm-double4"))]
core::arch::global_asm!(
    include_str!("fe51_product.inc"),
    include_str!("double4.S"),
    options(raw)
);

#[cfg(feature = "verify-asm-double4")]
core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/double4-checked.S")));

#[cfg(not(feature = "verify-asm-cached-add"))]
core::arch::global_asm!(
    include_str!("fe51_product.inc"),
    include_str!("add_cached.S"),
    options(raw)
);

#[cfg(feature = "verify-asm-cached-add")]
core::arch::global_asm!(include_str!(concat!(
    env!("OUT_DIR"),
    "/cached-add-checked.S"
)));

// These entries share private IFMA field kernels and the encoded-point layout.
core::arch::global_asm!(
    include_str!("torsion.S"),
    include_str!("pow22523.inc"),
    include_str!("point_encoding.inc"),
    include_str!("dalek_recompress.S"),
    include_str!("post_hash.inc"),
    include_str!("zip215.S"),
    include_str!("dalek.S"),
    include_str!("key_table.S"),
    include_str!("decompress_r.S"),
    include_str!("verify_batch.S"),
    options(raw)
);
