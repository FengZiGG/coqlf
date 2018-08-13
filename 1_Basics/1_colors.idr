data Rgb = Red | Green | Blue

data Color : Type where
    Black : Color
    White : Color
    Primary : Rgb -> Color

monochrome : Color -> Bool
monochrome Black = True
monochrome White = True
monochrome _     = False

isred : Color -> Bool
isred (Primary Red) = True
isred _             = False
