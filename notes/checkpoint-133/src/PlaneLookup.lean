import PlaneData0
import PlaneData1
import PlaneData2
import PlaneData3
import PlaneData4
import PlaneData5
import PlaneData6

namespace Checkpoint133.Plane.Data

def chunks : Array (Array Entry) := #[block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32,block33,block34,block35,block36,block37,block38,block39,block40,block41,block42,block43,block44,block45,block46,block47,block48,block49,block50,block51,block52,block53,block54,block55,block56,block57,block58,block59,block60,block61,block62,block63,block64,block65,block66,block67,block68,block69,block70,block71,block72,block73,block74,block75,block76]
def lookup (i : ℕ) : Entry := (chunks.getD (i/64) #[]).getD (i%64) default

end Checkpoint133.Plane.Data
