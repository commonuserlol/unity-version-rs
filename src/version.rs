use std::cmp::Ordering;
use std::fmt::{self, Display};
use std::sync::LazyLock;

use regex::Regex;
use thiserror::Error;

use crate::unity_type::UnityVersionType;

/// The regex used to parse the version.
///
/// Thanks to [AssetRipper.Primitives](https://github.com/AssetRipper/AssetRipper.Primitives/blob/master/AssetRipper.Primitives/UnityVersionRegexes.cs) for the regex.
static UNITY_VERSION_REGEX: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"([0-9]+)\.([0-9]+)\.([0-9]+)\.?([abcfpx]+)([0-9]+)").unwrap());

/// Represents a Unity version.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct UnityVersion {
    /// The major version number.
    ///
    /// For example, in the version `2020.2.1f1`, the major version is `2020``.
    major: u16,

    /// The minor version number.
    ///
    /// For example, in the version `2020.2.1f1`, the minor version is `2`.
    minor: u8,

    /// The build version number.
    ///
    /// For example, in the version `2020.2.1f1`, the build version is `1`.
    build: u8,

    /// The type of the version.
    ///
    /// For example, in the version `2020.2.1f1`, the type is [UnityVersionType::Final].
    ty: UnityVersionType,

    /// The type number of the version.
    ///
    /// For example, in the version `2020.2.1f1`, the type number is `1``.
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
                UnityVersionType::try_from(caps.get($i).ok_or($err)?.as_str().chars().nth(0).ok_or($err)?).or(Err($err))?
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

    /// Returns the version string, such as `2020.2.1f1`.
    #[inline]
    pub fn version(&self) -> String {
        format!("{}.{}.{}{}{}", self.major, self.minor, self.build, self.ty, self.type_number)
    }

    /// Returns the major version number.
    #[inline]
    pub fn major(&self) -> u16 {
        self.major
    }

    /// Returns the minor version number.
    #[inline]
    pub fn minor(&self) -> u8 {
        self.minor
    }

    /// Returns the build version number.
    #[inline]
    pub fn build(&self) -> u8 {
        self.build
    }

    /// Returns the type of the version.
    #[inline]
    pub fn ty(&self) -> &UnityVersionType {
        &self.ty
    }

    /// Returns the type number of the version.
    #[inline]
    pub fn type_number(&self) -> u8 {
        self.type_number
    }
}

/// The error type for [UnityVersion].
#[derive(Debug, Error, PartialEq, Eq)]
pub enum UnityVersionError {
    /// The regex used to parse the version failed.
    #[error("The wrong version was specified")]
    InvalidVersion,
    /// The regex used to parse the version or parse the number failed.
    #[error("The wrong major was specified")]
    InvalidMajor,
    /// The regex used to parse the version or parse the number failed.
    #[error("The wrong minor was specified")]
    /// The regex used to parse the version or parse the number failed.
    InvalidMinor,
    #[error("The wrong build was specified")]
    /// The regex used to parse the version or parse the number failed.
    InvalidBuild,
    /// The build type contains an invalid character.
    #[error("The wrong type was specified")]
    InvalidType,
    /// The regex used to parse the version or parse the number failed.
    #[error("The wrong type number was specified")]
    InvalidTypeNumber,
}

/// A macro to quickly create a [UnityVersion].
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
            UnityVersion::try_from("2020.2.1f1"),
            Ok(UnityVersion::new(2020, 2, 1, UnityVersionType::Final, 1))
        );
        assert_eq!(
            UnityVersion::try_from("2019.4.10b5"),
            Ok(UnityVersion::new(2019, 4, 10, UnityVersionType::Beta, 5))
        );
        assert_eq!(
            UnityVersion::try_from("2021.1.0a3"),
            Ok(UnityVersion::new(2021, 1, 0, UnityVersionType::Alpha, 3))
        );
        assert_eq!(
            UnityVersion::try_from("2018.3.12p2"),
            Ok(UnityVersion::new(2018, 3, 12, UnityVersionType::Patch, 2))
        );
        assert_eq!(
            UnityVersion::try_from("2017.2.0c0"),
            Ok(UnityVersion::new(2017, 2, 0, UnityVersionType::China, 0))
        );
        assert_eq!(
            UnityVersion::try_from("2022.5.1x10"),
            Ok(UnityVersion::new(2022, 5, 1, UnityVersionType::Experimental, 10))
        );
        assert_eq!(UnityVersion::try_from("invalid.version.string"), Err(UnityVersionError::InvalidVersion));

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
        assert!(unity_version!(2020, 1) == unity_version!(2020, 1));
        assert!(unity_version!(2020, 1, 1) == unity_version!(2020, 1, 1));
        assert!(unity_version!(2020, 1, 1, UnityVersionType::Beta) == unity_version!(2020, 1, 1, UnityVersionType::Beta));
        assert!(unity_version!(2020, 1, 1, UnityVersionType::Beta, 1) == unity_version!(2020, 1, 1, UnityVersionType::Beta, 1));
    }

    #[test]
    fn into_string() {
        assert_eq!("2020.1.1a1", unity_version!(2020, 1, 1, UnityVersionType::Alpha, 1).version());
        assert_eq!("2020.1.1b2", unity_version!(2020, 1, 1, UnityVersionType::Beta, 2).version());
        assert_eq!("2020.1.1c3", unity_version!(2020, 1, 1, UnityVersionType::China, 3).version());
        assert_eq!("2020.1.1f4", unity_version!(2020, 1, 1, UnityVersionType::Final, 4).version());
        assert_eq!("2020.1.1p5", unity_version!(2020, 1, 1, UnityVersionType::Patch, 5).version());
        assert_eq!("2020.1.1x6", unity_version!(2020, 1, 1, UnityVersionType::Experimental, 6).version());
    }
}
