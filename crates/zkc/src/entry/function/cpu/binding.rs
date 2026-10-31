use super::{FunctionInterface, Result, error};

impl FunctionInterface {
    pub(super) fn check_native_input(&self, schema: &super::Schema) -> Result<()> {
        self.check_input(schema)?;
        super::require(
            schema.leaves.iter().all(|leaf| {
                zkc_runtime::vm::LogicalType::parse(leaf)
                    .is_ok_and(|ty| ty.is_native_message_data())
            }),
            "entry-input-codec",
        )
    }

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
