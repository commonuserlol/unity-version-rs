use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
};

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub enum UnityVersionType {
    #[default]
    Alpha,
    Beta,
    China,
    Final,
    Patch,
    Experimental,
}

impl Display for UnityVersionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

impl TryFrom<char> for UnityVersionType {
    type Error = ();

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            'a' => Ok(Self::Alpha),
            'b' => Ok(Self::Beta),
            'c' => Ok(Self::China),
            'f' => Ok(Self::Final),
            'p' => Ok(Self::Patch),
            'x' => Ok(Self::Experimental),
            _ => Err(()),
        }
    }
}

impl Into<char> for UnityVersionType {
    fn into(self) -> char {
        self.as_ref().to_owned()
    }
}

impl AsRef<char> for UnityVersionType {
    fn as_ref(&self) -> &char {
        match self {
            Self::Alpha => &'a',
            Self::Beta => &'b',
            Self::China => &'c',
            Self::Final => &'f',
            Self::Patch => &'p',
            Self::Experimental => &'x',
        }
    }
}

impl PartialOrd for UnityVersionType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UnityVersionType {
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            Self::Alpha => match other {
                Self::Alpha => Ordering::Equal,
                _ => Ordering::Less,
            },
            Self::Beta => match other {
                Self::Alpha => Ordering::Greater,
                Self::Beta => Ordering::Equal,
                _ => Ordering::Less,
            },
            Self::China => match other {
                Self::Alpha | Self::Beta => Ordering::Greater,
                Self::China => Ordering::Equal,
                _ => Ordering::Less,
            },
            Self::Final => match other {
                Self::Alpha | Self::Beta | Self::China => Ordering::Greater,
                Self::Final => Ordering::Equal,
                _ => Ordering::Less,
            },
            Self::Patch => match other {
                Self::Experimental => Ordering::Less,
                Self::Patch => Ordering::Equal,
                _ => Ordering::Greater,
            },
            Self::Experimental => match other {
                Self::Experimental => Ordering::Equal,
                _ => Ordering::Greater,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_be_less() {
        assert!(UnityVersionType::Alpha < UnityVersionType::Beta);
        assert!(UnityVersionType::Beta < UnityVersionType::China);
        assert!(UnityVersionType::China < UnityVersionType::Final);
        assert!(UnityVersionType::Final < UnityVersionType::Patch);
        assert!(UnityVersionType::Patch < UnityVersionType::Experimental);
    }

    #[test]
    fn should_be_greater() {
        assert!(UnityVersionType::Beta > UnityVersionType::Alpha);
        assert!(UnityVersionType::China > UnityVersionType::Beta);
        assert!(UnityVersionType::Final > UnityVersionType::China);
        assert!(UnityVersionType::Patch > UnityVersionType::Final);
        assert!(UnityVersionType::Experimental > UnityVersionType::Patch);
    }

    #[test]
    fn from_char() {
        assert_eq!(Ok(UnityVersionType::Alpha), UnityVersionType::try_from('a'));
        assert_eq!(Ok(UnityVersionType::Beta), UnityVersionType::try_from('b'));
        assert_eq!(Ok(UnityVersionType::China), UnityVersionType::try_from('c'));
        assert_eq!(Ok(UnityVersionType::Final), UnityVersionType::try_from('f'));
        assert_eq!(Ok(UnityVersionType::Patch), UnityVersionType::try_from('p'));
        assert_eq!(Ok(UnityVersionType::Experimental), UnityVersionType::try_from('x'));
        assert_eq!(Err(()), UnityVersionType::try_from('y'));
    }

    #[test]
    fn to_char() {
        assert_eq!('a', UnityVersionType::Alpha.into());
        assert_eq!('b', UnityVersionType::Beta.into());
        assert_eq!('c', UnityVersionType::China.into());
        assert_eq!('f', UnityVersionType::Final.into());
        assert_eq!('p', UnityVersionType::Patch.into());
        assert_eq!('x', UnityVersionType::Experimental.into());
    }
}
