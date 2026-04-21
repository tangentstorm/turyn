use std::fmt;
use std::time::Duration;

/// A mass value measured in **search-space bits**:
/// `log2(|cube|)` for the sub-cube it represents.
///
/// `total_mass` for a run is `log2` of the fully-free search space
/// enumeration count. `covered_mass` accumulates the log-size of
/// every sub-cube eliminated (by a solved leaf, a deferred credit,
/// or a forced-literal shrink). Throughput is therefore bits/second
/// and TTC is `remaining_bits / bits_per_sec` — one dimensionless
/// unit across every mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, PartialOrd)]
pub struct MassValue(pub f64);

impl MassValue {
    pub const ZERO: Self = Self(0.0);

    pub fn saturating_sub(self, rhs: Self) -> Self {
        Self((self.0 - rhs.0).max(0.0))
    }
}

impl fmt::Display for MassValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.6}", self.0)
    }
}

/// Quality label for a published TTC estimate.
///
/// * [`TtcQuality::Direct`] — computed as `elapsed /
///   cumulative_coverage`, where cumulative coverage is the product
///   of per-level covered fractions observed so far. Exact iff the
///   run will continue to forced-literal proportions the sample
///   implies.
/// * [`TtcQuality::Projected`] — computed from an explicit model of
///   the remaining search (e.g. branching-factor extrapolation).
///   Used when coverage is too small to trust the direct form.
/// * [`TtcQuality::Hybrid`] — blend; typically the direct form with
///   projected smoothing on the tail.
///
/// Older enum name retained via the `CoverageQuality` alias for
/// existing call sites; migrate to `TtcQuality`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TtcQuality {
    Direct,
    Projected,
    Hybrid,
}

pub type CoverageQuality = TtcQuality;

impl TtcQuality {
    /// Backward-compat alias: the original enum spelled this
    /// variant `Exact`. The three `Direct | Projected | Hybrid`
    /// labels from TELEMETRY.md replace it directly.
    #[allow(non_upper_case_globals)]
    pub const Exact: Self = TtcQuality::Direct;
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct MassDelta {
    pub covered_exact: MassValue,
    pub covered_partial: MassValue,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MassSnapshot {
    pub total: MassValue,
    pub covered_exact: MassValue,
    pub covered_partial: MassValue,
}

impl MassSnapshot {
    pub fn new(total: MassValue) -> Self {
        Self {
            total,
            covered_exact: MassValue::ZERO,
            covered_partial: MassValue::ZERO,
        }
    }

    pub fn apply_delta(&mut self, delta: MassDelta) {
        self.covered_exact = MassValue((self.covered_exact.0 + delta.covered_exact.0).max(0.0));
        self.covered_partial =
            MassValue((self.covered_partial.0 + delta.covered_partial.0).max(0.0));

        if self.covered_exact.0 > self.total.0 {
            self.covered_exact = self.total;
        }

        let partial_cap = (self.total.0 - self.covered_exact.0).max(0.0);
        if self.covered_partial.0 > partial_cap {
            self.covered_partial = MassValue(partial_cap);
        }
    }

    pub fn covered(&self) -> MassValue {
        MassValue(self.covered_exact.0 + self.covered_partial.0)
    }

    pub fn remaining(&self) -> MassValue {
        self.total.saturating_sub(self.covered())
    }

    pub fn throughput_per_sec(&self, elapsed: Duration) -> MassValue {
        let secs = elapsed.as_secs_f64();
        if secs <= f64::EPSILON {
            MassValue::ZERO
        } else {
            MassValue(self.covered().0 / secs)
        }
    }

    pub fn ttc(&self, elapsed: Duration) -> Option<Duration> {
        let rate = self.throughput_per_sec(elapsed).0;
        if rate <= f64::EPSILON {
            None
        } else {
            Some(Duration::from_secs_f64(self.remaining().0 / rate))
        }
    }
}

pub trait SearchMassModel: Send + Sync {
    fn total_mass(&self) -> MassValue;
    fn covered_mass(&self) -> MassValue;
    fn quality(&self) -> CoverageQuality;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remaining_mass_never_negative() {
        let mut snap = MassSnapshot::new(MassValue(10.0));
        snap.apply_delta(MassDelta {
            covered_exact: MassValue(12.0),
            covered_partial: MassValue(1.0),
        });
        assert_eq!(snap.covered().0, 10.0);
        assert_eq!(snap.remaining().0, 0.0);
    }

    #[test]
    fn covered_mass_is_monotone_for_positive_deltas() {
        let mut snap = MassSnapshot::new(MassValue(10.0));
        let mut prev = snap.covered().0;
        for _ in 0..4 {
            snap.apply_delta(MassDelta {
                covered_exact: MassValue(1.0),
                covered_partial: MassValue(0.5),
            });
            assert!(snap.covered().0 >= prev);
            prev = snap.covered().0;
        }
    }

    #[test]
    fn ttc_is_none_when_rate_is_zero() {
        let snap = MassSnapshot::new(MassValue(10.0));
        assert!(snap.ttc(Duration::from_secs(5)).is_none());
    }
}
