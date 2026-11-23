core::arch::global_asm!(include_str!("prepare_chunk.S"), options(raw));

/// Workspace required by the batch entry points. Assembly owns the contents.
#[repr(C, align(64))]
pub(crate) struct ChunkScratch([u8; 25_344]);
