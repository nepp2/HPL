
#[no_mangle]
pub extern "C" fn blahblah(a : i64, b : i64) -> i64 {
  a - b
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(crate::blahblah(2, 2), 4);
    }
}
