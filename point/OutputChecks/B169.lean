import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block169_checked : centerBlock 169 = true := by decide +kernel
#print axioms block169_checked
end PythiaCert.Output
