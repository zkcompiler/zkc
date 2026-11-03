use super::{FunctionInterface, Result, error};

impl FunctionInterface {
    fn result_types(&self) -> Result<Vec<zkc_runtime::vm::PhysicalType>> {
        self.signature()
            .result
            .leaves
            .iter()
            .map(|leaf| {
                let logical = zkc_runtime::vm::LogicalType::parse(leaf)
                    .map_err(|_| error("entry-output-codec"))?;
                zkc_runtime::vm::PhysicalType::default_for(logical)
                    .map_err(|_| error("entry-output-codec"))
            })
            .collect()
    }
    /// Check result codecs against the explicitly selected CPU installation.
    pub fn check_result_encoding(&self, installation: &zkc_cpu::CpuInstallation) -> Result<()> {
        crate::entry::value::check_readable_schema(&self.signature().result)
            .map_err(|e| error(&e))?;
        if self
            .result_types()?
            .iter()
            .all(|ty| installation.supports_wire(ty))
        {
            Ok(())
        } else {
            Err(error("entry-output-codec"))
        }
    }
}
