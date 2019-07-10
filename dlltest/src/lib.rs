
#[no_mangle]
pub extern "C" fn function_from_dll(a : i64, b : i64) -> i64 {
  a + b
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(crate::function_from_dll(2, 2), 4);
    }
}
