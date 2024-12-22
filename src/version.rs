use std::cmp::Ordering;
use std::fmt::{self, Display};
use std::sync::LazyLock;

use regex::Regex;
use thiserror::Error;

use crate::unity_type::UnityVersionType;

static UNITY_VERSION_REGEX: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"([0-9]+)\.([0-9]+)\.([0-9]+)\.?([abcfpx]+)([0-9]+)").unwrap());

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct UnityVersion {
    /// Major release number
    major: u16,
    /// Minor release number
    minor: u8,
    /// Build release number
    build: u8,
    /// Release type
    ty: UnityVersionType,
    /// Release type number
    type_number: u8,
}

impl Display for UnityVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unity {}", self.version())
    }
}

impl PartialOrd for UnityVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UnityVersion {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.major > other.major {
            return Ordering::Greater;
        } else if self.major < other.major {
            return Ordering::Less;
        }

        if self.minor > other.minor {
            return Ordering::Greater;
        } else if self.minor < other.minor {
            return Ordering::Less;
        }

        if self.build > other.build {
            return Ordering::Greater;
        } else if self.build < other.build {
            return Ordering::Less;
        }

        let type_cmp = self.ty.cmp(&other.ty);
        if type_cmp == Ordering::Equal {
            if self.type_number > other.type_number {
                Ordering::Greater
            } else if self.type_number < other.type_number {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        } else {
            type_cmp
        }
    }
}

impl TryFrom<&str> for UnityVersion {
    type Error = UnityVersionError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let caps = UNITY_VERSION_REGEX.captures(value).ok_or(UnityVersionError::InvalidVersion)?;

        macro_rules! parse {
            ($i:expr, $err:expr) => {
                caps.get($i).ok_or($err)?.as_str().parse().or(Err($err))?
            };
            ($i:expr, $char:expr, $err:expr) => {
                UnityVersionType::from(caps.get($i).ok_or($err)?.as_str().chars().nth(0).ok_or($err)?)
            };
        }

        Ok(UnityVersion {
            major: parse!(1, UnityVersionError::InvalidMajor),
            minor: parse!(2, UnityVersionError::InvalidMinor),
            build: parse!(3, UnityVersionError::InvalidBuild),
            ty: parse!(4, 0, UnityVersionError::InvalidType),
            type_number: parse!(5, UnityVersionError::InvalidTypeNumber),
        })
    }
}

impl UnityVersion {
    pub fn new(major: u16, minor: u8, build: u8, ty: UnityVersionType, type_number: u8) -> Self {
        Self {
            major,
            minor,
            build,
            ty,
            type_number,
        }
    }

    #[inline]
    pub fn version(&self) -> String {
        format!("{}.{}.{}{}{}", self.major, self.minor, self.build, self.ty, self.type_number)
    }

    #[inline]
    pub fn minor(&self) -> u8 {
        self.minor
    }

    #[inline]
    pub fn build(&self) -> u8 {
        self.build
    }

    #[inline]
    pub fn ty(&self) -> &UnityVersionType {
        &self.ty
    }

    #[inline]
    pub fn type_number(&self) -> u8 {
        self.type_number
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum UnityVersionError {
    #[error("The wrong version was specified")]
    InvalidVersion,
    #[error("The wrong major was specified")]
    InvalidMajor,
    #[error("The wrong minor was specified")]
    InvalidMinor,
    #[error("The wrong build was specified")]
    InvalidBuild,
    #[error("The wrong type was specified")]
    InvalidType,
    #[error("The wrong type number was specified")]
    InvalidTypeNumber,
}

#[macro_export]
macro_rules! unity_version {
    ($major: expr, $minor: expr, $build: expr, $type: expr, $type_number: expr) => {
        UnityVersion::new($major, $minor, $build, $type, $type_number)
    };
    ($major: expr, $minor: expr, $build: expr, $type: expr) => {
        UnityVersion::new($major, $minor, $build, $type, 0)
    };
    ($major: expr, $minor: expr, $build: expr) => {
        UnityVersion::new($major, $minor, $build, UnityVersionType::Alpha, 0)
    };
    ($major: expr, $minor: expr) => {
        UnityVersion::new($major, $minor, 0, UnityVersionType::Alpha, 0)
    };
    ($major: expr) => {
        UnityVersion::new($major, 0, 0, UnityVersionType::Alpha, 0)
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_from_str() -> Result<(), UnityVersionError> {
        assert_eq!(
            UnityVersion::new(2020, 1, 1, UnityVersionType::Alpha, 1),
            UnityVersion::try_from("2020.1.1a1")?
        );
        assert_eq!(Err(UnityVersionError::InvalidVersion), UnityVersion::try_from("2020.1.1a"));

        Ok(())
    }

    #[test]
    fn should_be_less() {
        assert!(unity_version!(2020) < unity_version!(2021));
        assert!(unity_version!(2021) < unity_version!(2021, 1));
        assert!(unity_version!(2021, 1) < unity_version!(2021, 2, 3));
        assert!(unity_version!(2021, 2, 3, UnityVersionType::Beta) < unity_version!(2021, 2, 3, UnityVersionType::Final));
        assert!(unity_version!(2021, 2, 3, UnityVersionType::Final, 1) < unity_version!(2021, 2, 3, UnityVersionType::Final, 2));
    }

    #[test]
    fn should_be_greater() {
        assert!(unity_version!(2020) > unity_version!(2019));
        assert!(unity_version!(2020, 1) > unity_version!(2020));
        assert!(unity_version!(2020, 1, 1) > unity_version!(2020, 1));
        assert!(unity_version!(2020, 1, 1, UnityVersionType::Beta) > unity_version!(2020, 1, 1));
        assert!(unity_version!(2020, 1, 1, UnityVersionType::Beta, 1) > unity_version!(2020, 1, 1, UnityVersionType::Beta));
    }

    #[test]
    fn should_be_equal() {
        assert!(unity_version!(2020) == unity_version!(2020));
    }

    #[test]
    fn into_string() {
        assert_eq!("2020.1.1x5", unity_version!(2020, 1, 1, UnityVersionType::Experimental, 5).version());
    }
}
