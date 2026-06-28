# RootVision 源代码清单

**软件名称**: RootVision（根图分析）  
**版本**: v1.0  
**文件**: rootvision_core.py（核心分析引擎）  
**用途**: 软件著作权申请源代码交存

---

## 文件说明

`rootvision_core.py` 是 RootVision 的核心分析引擎模块，包含完整的根系图像分析算法实现。该文件从主程序中提取，仅包含核心算法类 `RootSystemAnalyzer`，不含 GUI 界面代码，适用于软件著作权源代码交存。

**模块结构**:
- Python 版本检查 (`check_python_version`)
- 依赖库检查 (`check_dependencies`)
- 核心分析类 (`RootSystemAnalyzer`) — 包含图像加载、增强、分割、过滤、根系计数、参数计算等全部分析方法

---

## 源代码清单

以下为 `rootvision_core.py` 完整源代码，按行号排列。

> 注：完整源代码请查看文件 `rootvision_core.py`（共 1549 行），此处为代码结构概览。

### 文件开头：版权声明与版本信息

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根图分析 - RootVision
版本: v1.0
"""
__version__ = "1.0"

# 核心分析引擎 - 用于软件著作权申请
# Core Analysis Engine - For Software Copyright Registration
```

### 依赖导入 (第13-33行)

```python
import sys, os, json, csv
from PIL import Image, ImageTk, ImageDraw, ImageFont
import threading, queue, time
from datetime import datetime
import traceback, warnings, colorsys, itertools, math
import numpy as np
import multiprocessing
from concurrent.futures import ProcessPoolExecutor, as_completed, TimeoutError
import gc, psutil
```

### Python版本检查 (第37-45行)

```python
def check_python_version():
    """检查Python版本兼容性"""
    python_version = sys.version_info
    if python_version < (3, 8):
        print(f"警告: 当前Python版本 {python_version.major}.{python_version.minor}")
        print("建议升级到Python 3.8或更高版本")
    return True
```

### 依赖库检查 (第48-119行)

`check_dependencies()` — 检查并导入所需第三方库：OpenCV、NumPy、scikit-image、SciPy、Matplotlib、Pillow、psutil。缺少库时弹出错误提示。

### 核心类 RootSystemAnalyzer (第149-1544行)

主要属性：
- `DEFAULT_DIAMETER_CLASSES` — 默认5级根系直径分类
- `pixel_to_mm` — 比例尺转换因子
- `results` — 分析结果字典
- `root_parameters` — 根系形态参数
- `filter_stats` — 过滤统计
- `roi_active` — ROI 区域（图像坐标）

主要方法：

| 方法名 | 功能 |
|--------|------|
| `_get_diameter_classes()` | 返回有效直径分级列表 |
| `_get_class_suffix_keys()` | 生成分级键名 |
| `load_image()` | 加载图像文件 |
| `enhance_image()` | 图像增强处理 |
| `segment_image()` | OTSU 二值化分割 |
| `enhance_scanned_image()` | 扫描图像专用优化 |
| `filter_regions()` | 形态学过滤（面积/长度/长宽比） |
| `skeletonize()` | 骨架化提取 |
| `count_roots()` | 连通组件分析计数 |
| `calculate_parameters()` | 计算全部根系参数 |
| `_classify_roots_by_diameter()` | 按直径分级统计 |
| `generate_overlay_image()` | 生成标注叠加图 |
| `generate_detailed_report_image()` | 生成详细报告图 |
| `save_results_csv()` | 导出 CSV 数据 |
| `save_results_json()` | 导出 JSON 数据 |
| `analyze_single_image_static()` | 静态方法：单张图像全流程分析 |

---

## 代码统计

| 项目 | 数量 |
|------|------|
| 文件总行数 | 1549 |
| 核心类数 | 1 (RootSystemAnalyzer) |
| 核心方法数 | 30+ |
| 辅助函数数 | 2 (check_python_version, check_dependencies) |
| 依赖库数 | 7 (cv2, numpy, skimage, scipy, matplotlib, PIL, psutil) |

---

*本文件为 RootVision v1.0 软件著作权申请材料之一，包含核心分析引擎完整源代码。*
