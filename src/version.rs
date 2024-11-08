use std::cmp::Ordering;
use std::fmt::{self, Display};
use std::sync::LazyLock;

use regex::Regex;

use crate::unity_type::UnityVersionType;

static UNITY_VERSION_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"([0-9]+)\.([0-9]+)\.([0-9]+)\.?([abcfpx]+)([0-9]+)").unwrap());

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct UnityVersion {
    /// Major release number
    pub major: u16,
    /// Minor release number
    pub minor: u8,
    /// Build release number
    pub build: u8,
    /// Release type
    pub r#type: UnityVersionType,
    /// Release type number
    pub type_number: u8,
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

        let type_cmp = self.r#type.cmp(&other.r#type);
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

impl From<&str> for UnityVersion {
    fn from(value: &str) -> Self {
        let caps = UNITY_VERSION_REGEX.captures(value).unwrap();

        UnityVersion {
            major: caps.get(1).unwrap().as_str().parse().unwrap(),
            minor: caps.get(2).unwrap().as_str().parse().unwrap(),
            build: caps.get(3).unwrap().as_str().parse().unwrap(),
            r#type: UnityVersionType::from(caps.get(4).unwrap().as_str().chars().nth(0).unwrap()),
            type_number: caps.get(5).unwrap().as_str().parse().unwrap(),
        }
    }
}

impl UnityVersion {
    pub fn new(
        major: u16,
        minor: u8,
        build: u8,
        r#type: UnityVersionType,
        type_number: u8,
    ) -> Self {
        Self {
            major,
            minor,
            build,
            r#type,
            type_number,
        }
    }

    #[inline]
    pub fn version(&self) -> String {
        format!(
            "{}.{}.{}{}{}",
            self.major, self.minor, self.build, self.r#type, self.type_number
        )
    }
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
    fn parse_from_str() {
        assert_eq!(
            UnityVersion::new(2020, 1, 1, UnityVersionType::Alpha, 1),
            UnityVersion::from("2020.1.1a1")
        )
    }

    #[test]
    fn should_be_less() {
        assert!(unity_version!(2020) < unity_version!(2021));
        assert!(unity_version!(2021) < unity_version!(2021, 1));
        assert!(unity_version!(2021, 1) < unity_version!(2021, 2, 3));
        assert!(
            unity_version!(2021, 2, 3, UnityVersionType::Beta)
                < unity_version!(2021, 2, 3, UnityVersionType::Final)
        );
        assert!(
            unity_version!(2021, 2, 3, UnityVersionType::Final, 1)
                < unity_version!(2021, 2, 3, UnityVersionType::Final, 2)
        );
    }

    #[test]
    fn should_be_greater() {
        assert!(unity_version!(2020) > unity_version!(2019));
        assert!(unity_version!(2020, 1) > unity_version!(2020));
        assert!(unity_version!(2020, 1, 1) > unity_version!(2020, 1));
        assert!(unity_version!(2020, 1, 1, UnityVersionType::Beta) > unity_version!(2020, 1, 1));
        assert!(
            unity_version!(2020, 1, 1, UnityVersionType::Beta, 1)
                > unity_version!(2020, 1, 1, UnityVersionType::Beta)
        );
    }

    #[test]
    fn should_be_equal() {
        assert!(unity_version!(2020) == unity_version!(2020));
    }

    #[test]
    fn into_string() {
        assert_eq!(
            "2020.1.1x5",
            unity_version!(2020, 1, 1, UnityVersionType::Experimental, 5).version()
        );
    }
}
