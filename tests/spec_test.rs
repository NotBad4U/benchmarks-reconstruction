use std::panic::AssertUnwindSafe;
use std::process::Command;
use std::process::ExitStatus;

use file_test_runner::collect_and_run_tests;
use file_test_runner::collection::CollectedTest;
use file_test_runner::collection::CollectOptions;
use file_test_runner::collection::strategies::TestPerFileCollectionStrategy;
use file_test_runner::RunOptions;
use file_test_runner::TestResult;

fn main() {
  collect_and_run_tests(
    CollectOptions {
      base: "tests/benchs".into(),
      strategy: Box::new(TestPerFileCollectionStrategy {
       file_pattern: Some("^.*\\.alethe$".to_owned())
      }),
      filter_override: None,
    },
    RunOptions {
      parallel: true,
    },
    // custom function to run the test...
    |test| {
      // * do something like this
      // * or do some checks yourself and return a value like TestResult::Passed
      // * or use `TestResult::from_maybe_panic_or_result` to combine both of the above
      // TestResult::from_maybe_panic(AssertUnwindSafe(|| {
        
      // }))
      let status =  run_test(test);

      if status.code().unwrap() == 0 {
        TestResult::Passed
      } else {
        TestResult::Failed { output: vec![] }
      }
    }
  )
}

// The `test` object only contains the test name and
// the path to the file on the file system which you can
// then use to determine how to run your test
fn run_test(test: &CollectedTest) -> ExitStatus {
  // Properties:
  // * `test.name` - Fully resolved name of the test.
  // * `test.path` - Path to the test file this test is associated with.
  // * `test.data` - Data associated with the test that may have been set

  let file_name = &test.name;
  let alethe_file = test.path.clone();
  let problem_file = test.path.with_extension("smt2");

  let status = Command::new("carcara")
    .arg("check")
    .args(["--log", "off"])
    .arg("-i")
    .arg(alethe_file)
    .arg(problem_file)
    .status()
    .expect(format!("failed running carcara check on {}", file_name).as_str());
  status 
}