use std::{
    cmp::Ordering,
    fmt::{Display, Formatter},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnityVersionType {
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

impl From<char> for UnityVersionType {
    fn from(value: char) -> Self {
        match value {
            'a' => Self::Alpha,
            'b' => Self::Beta,
            'c' => Self::China,
            'f' => Self::Final,
            'p' => Self::Patch,
            'x' => Self::Experimental,
            _ => unreachable!(),
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
        assert_eq!(UnityVersionType::Alpha, UnityVersionType::from('a'));
        assert_eq!(UnityVersionType::Beta, UnityVersionType::from('b'));
        assert_eq!(UnityVersionType::China, UnityVersionType::from('c'));
        assert_eq!(UnityVersionType::Final, UnityVersionType::from('f'));
        assert_eq!(UnityVersionType::Patch, UnityVersionType::from('p'));
        assert_eq!(UnityVersionType::Experimental, UnityVersionType::from('x'));
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
