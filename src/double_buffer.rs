use core::{mem::MaybeUninit, slice};

use alloc::{boxed::Box, vec::Vec};

/// Double buffer. Wraps a mutable slice and allocates a scratch memory of the same size, so that
/// elements can be freely scattered from buffer to buffer.
///
/// # Drop behavior
///
/// Drop ensures that the mutable slice this buffer was constructed with contains all the original
/// elements.
pub struct DoubleBuffer<'a, T> {
    slice: &'a mut [MaybeUninit<T>],
    scratch: Box<[MaybeUninit<T>]>,
    slice_is_write: bool,
}

impl<'a, T> DoubleBuffer<'a, T> {
    /// Creates a double buffer, allocating a scratch buffer of the same length as the input slice.
    ///
    /// The supplied slice becomes the read buffer, the scratch buffer becomes the write buffer.
    pub fn new(slice: &'a mut [T]) -> Self {
        let slice = unsafe {
            // SAFETY: `[MaybeUninit<T>]` and `[T]` have the same layout.
            // The Drop impl ensures that the slice contains all the original elements.
            slice::from_raw_parts_mut(slice.as_mut_ptr() as *mut MaybeUninit<T>, slice.len())
        };
        let scratch = {
            let mut v = Vec::with_capacity(slice.len());
            // SAFETY: we just allocated this capacity and MaybeUninit can be garbage.
            unsafe {
                v.set_len(slice.len());
            }
            v.into_boxed_slice()
        };
        DoubleBuffer {
            slice,
            scratch,
            slice_is_write: false,
        }
    }

    /// Scatters the elements from the read buffer to the computed indices in
    /// the write buffer. The read buffer is iterated from the beginning.
    ///
    /// Call `swap` after this function to commit the write buffer state.
    ///
    /// # Panics
    ///
    /// Panics if the closure returns `index >= buffer length`.
    pub fn scatter<F>(&mut self, mut indexer: F)
    where
        F: for<'t> FnMut(&'t T) -> usize,
    {
        let (read, write) = self.as_read_write_buffers();

        for t in read {
            let index = indexer(t);
            let write_ptr = write[index].as_mut_ptr();
            unsafe {
                // SAFETY: both pointers are valid for T, aligned, and nonoverlapping
                write_ptr.copy_from_nonoverlapping(t as *const T, 1);
            }
        }
    }

    /// Returns the current read and write buffers.
    fn as_read_write_buffers(&mut self) -> (&[T], &mut [MaybeUninit<T>]) {
        let (read, write): (&[MaybeUninit<T>], &mut [MaybeUninit<T>]) = if self.slice_is_write {
            (self.scratch.as_ref(), self.slice)
        } else {
            (self.slice, self.scratch.as_mut())
        };

        let read: &[T] = unsafe {
            // SAFETY `[MaybeUninit<T>]` and `[T]` have the same layout.
            // The read buffer is always initialized.
            &*(read as *const [MaybeUninit<T>] as *const [T])
        };

        (read, write)
    }

    /// Swaps the read and write buffer, committing the write buffer state.
    ///
    /// # Safety
    ///
    /// The caller must ensure that every element of the write buffer was
    /// written to before calling this function.
    pub unsafe fn swap(&mut self) {
        self.slice_is_write = !self.slice_is_write;
    }
}

/// Ensures that the input slice contains all the original elements.
impl<'a, T> Drop for DoubleBuffer<'a, T> {
    fn drop(&mut self) {
        if self.slice_is_write {
            // The input slice is the write buffer, copy the consistent state from the read buffer
            unsafe {
                // SAFETY: `scratch` is the read buffer, it is initialized. The length is the same.
                self.slice
                    .as_mut_ptr()
                    .copy_from_nonoverlapping(self.scratch.as_ptr(), self.slice.len());
            }
            self.slice_is_write = false;
        }
    }
}
