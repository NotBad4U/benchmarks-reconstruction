use std::panic::AssertUnwindSafe;

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
       file_pattern: None
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
      TestResult::from_maybe_panic(AssertUnwindSafe(|| {
       run_test(test);
      }))
    }
  )
}

// The `test` object only contains the test name and
// the path to the file on the file system which you can
// then use to determine how to run your test
fn run_test(test: &CollectedTest) {
  // Properties:
  // * `test.name` - Fully resolved name of the test.
  // * `test.path` - Path to the test file this test is associated with.
  // * `test.data` - Data associated with the test that may have been set
  //                 by the collection strategy.

  // helper function to get the text
  //let file_text = test.read_to_string().unwrap();
  let file_name = &test.name;
  let file_path = &test.path;
  println!("{} {}", file_name, file_path.to_str().unwrap());

  // now you may do whatever with the file text and
  // assert it using assert_eq! or whatever
}