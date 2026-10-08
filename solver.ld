ENTRY(_start)

SECTIONS
{
    . = 0;

    .text : ALIGN(4)
    {
        *(.text)
        *(.text.*)
    }

    .rodata : ALIGN(2)
    {
        *(.rodata)
        *(.rodata.*)
    }

    .data : ALIGN(4)
    {
        *(.data)
        *(.data.*)
        *(.sdata)
        *(.sdata.*)
    }

    .bss (NOLOAD) : ALIGN(4)
    {
        *(.bss)
        *(.bss.*)
        *(COMMON)
    }
}