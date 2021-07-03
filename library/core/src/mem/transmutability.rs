/// FIXME
#[unstable(feature = "transmutability", issue = "none")]
#[cfg_attr(not(bootstrap), lang = "transmute_trait")]
pub unsafe trait BikeshedIntrinsicFrom<Src, Context, const ASSUME: Assume>
where
    Src: ?Sized,
{
}

/// FIXME
#[unstable(feature = "transmutability", issue = "none")]
#[cfg_attr(not(bootstrap), lang = "transmute_opts")]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[non_exhaustive]
pub struct Assume {
    /// FIXME
    pub alignment: bool,
    /// FIXME
    pub lifetimes: bool,
    /// FIXME
    pub validity: bool,
    /// FIXME
    pub visibility: bool,
}

#[unstable(feature = "transmutability", issue = "none")]
impl Assume {
    /// FIXME
    pub const NOTHING: Self =
        Self { alignment: false, lifetimes: false, validity: false, visibility: false };

    /// FIXME
    pub const ALIGNMENT: Self = Self { alignment: true, ..Self::NOTHING };

    /// FIXME
    pub const LIFETIMES: Self = Self { lifetimes: true, ..Self::NOTHING };

    /// FIXME
    pub const VALIDITY: Self = Self { validity: true, ..Self::NOTHING };

    /// FIXME
    pub const VISIBILITY: Self = Self { validity: true, ..Self::NOTHING };
}

/// FIXME
#[unstable(feature = "transmutability", issue = "none")]
impl const core::ops::Add for Assume {
    type Output = Self;

    #[rustc_const_unstable(feature = "transmutability", issue = "none")]
    fn add(self, rhs: Self) -> Self {
        Self {
            alignment: self.alignment || rhs.alignment,
            lifetimes: self.lifetimes || rhs.lifetimes,
            validity: self.validity || rhs.validity,
            visibility: self.visibility || rhs.visibility,
        }
    }
}

/// FIXME
#[unstable(feature = "transmutability", issue = "none")]
impl const core::ops::Sub for Assume {
    type Output = Self;

    #[rustc_const_unstable(feature = "transmutability", issue = "none")]
    fn sub(self, rhs: Self) -> Self {
        Self {
            alignment: self.alignment && !rhs.alignment,
            lifetimes: self.lifetimes && !rhs.lifetimes,
            validity: self.validity && !rhs.validity,
            visibility: self.visibility && !rhs.visibility,
        }
    }
}
