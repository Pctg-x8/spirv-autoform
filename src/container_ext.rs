//! Useful Extended value containers

/// The Placeholder(Used by Vec::resize for padding lazily-initialized slots)
pub trait HasPlaceholder : Sized
{
	fn placeholder() -> Self;
}
/// Using Default as Placeholder
impl<T> HasPlaceholder for T where T: Default
{
	fn placeholder() -> Self { Self::default() }
}

pub mod autosize_vec
{
	use super::HasPlaceholder;
	use std::ops::{Deref, DerefMut};
	use std::fmt::{Debug, Formatter, Result as FmtResult};

	#[derive(Clone)]
	pub struct AutosizeVec<T: Clone + HasPlaceholder>(Vec<T>);
	impl<T: Clone + HasPlaceholder> AutosizeVec<T>
	{
		pub fn new() -> Self { AutosizeVec(Vec::new()) }
		pub fn entry_or<F: FnOnce() -> T>(&mut self, index: usize, inserter: F) -> &mut T
		{
			if self.0.len() <= index { self.set(index, inserter()); }
			&mut self.0[index]
		}
		pub fn set(&mut self, index: usize, value: T)
		{
			if self.0.len() <= index { self.0.resize(index, T::placeholder()); self.0.push(value); }
			else { self.0[index] = value; }
		}
	}
	impl<T: Clone + HasPlaceholder> Deref for AutosizeVec<T> { type Target = Vec<T>; fn deref(&self) -> &Self::Target { &self.0 } }
	impl<T: Clone + HasPlaceholder> DerefMut for AutosizeVec<T> { fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 } }
	impl<T: Debug + Clone + HasPlaceholder> Debug for AutosizeVec<T> { fn fmt(&self, fmt: &mut Formatter) -> FmtResult { Debug::fmt(&self.0, fmt) } }
}
pub use self::autosize_vec::AutosizeVec;
