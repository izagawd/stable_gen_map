use crate::numeric::Numeric;

#[derive(Clone,Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData<Idx, Generation>{
    pub(crate) idx: Idx,
    pub(crate) generation: Generation,
}
pub unsafe trait Key : Copy + From<KeyData<Self::Idx, Self::Gen>> {
    type Idx : Numeric;
    type Gen : Numeric;

    fn data(&self) -> KeyData<Self::Idx, Self::Gen>;
}



#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultKey{
    pub(crate) key_data: KeyData<u32,u32>,
}

impl From<KeyData<u32,u32>> for DefaultKey{
    fn from(key_data: KeyData<u32,u32>) -> Self {
        DefaultKey{key_data: key_data}
    }
}

unsafe impl Key for DefaultKey{
    type Idx = u32;
    type Gen = u32;

    fn data(&self) -> KeyData<u32,u32>{
        self.key_data
    }
}